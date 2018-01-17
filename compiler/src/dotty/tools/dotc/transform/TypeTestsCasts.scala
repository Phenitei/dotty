package dotty.tools.dotc
package transform

import core._
import Contexts._, Symbols._, Types._, Constants._, StdNames._, Decorators._, Definitions._
import ast.Trees._
import Erasure.Boxing._
import TypeErasure._
import ValueClasses._
import SymUtils._
import core.Flags._
import util.Positions._
import reporting.trace


/** This transform normalizes type tests and type casts,
 *  also replacing type tests with singleton argument type with reference equality check
 *  Any remaining type tests
 *   - use the object methods $isInstanceOf and $asInstanceOf
 *   - have a reference type as receiver
 *   - can be translated directly to machine instructions
 *
 *
 * Unfortunately this phase ended up being not Y-checkable unless types are erased. A cast to an ConstantType(3) or x.type
 * cannot be rewritten before erasure.
 */
object TypeTestsCasts {
  import ast.tpd._

  def interceptTypeApply(tree: TypeApply)(implicit ctx: Context): Tree = trace(s"transforming ${tree.show}", show = true) {
    tree.fun match {
      case fun @ Select(expr, selector) =>
        val sym = tree.symbol

        def isPrimitive(tp: Type) = tp.classSymbol.isPrimitiveValueClass

        def derivedTree(expr1: Tree, sym: Symbol, tp: Type) =
          cpy.TypeApply(tree)(expr1.select(sym).withPos(expr.pos), List(TypeTree(tp)))

        def foundCls = expr.tpe.widen.classSymbol
        // println(i"ta $tree, found = $foundCls")

        def inMatch =
          fun.symbol == defn.Any_typeTest ||  // new scheme
          expr.symbol.is(Case)                // old scheme

        def transformIsInstanceOf(expr:Tree, testType: Type, flagUnrelated: Boolean, wasQtype: Boolean = false): Tree = {
          def testCls = testType.classSymbol

          def unreachable(why: => String) =
            if (flagUnrelated)
              if (inMatch) ctx.error(em"this case is unreachable since $why", expr.pos)
              else ctx.warning(em"this will always yield false since $why", expr.pos)

          /** Are `foundCls` and `testCls` classes that allow checks
           *  whether a test would be always false?
           */
          def isCheckable =
            foundCls.isClass && testCls.isClass &&
            !(testCls.isPrimitiveValueClass && !foundCls.isPrimitiveValueClass) &&
               // if `test` is primitive but `found` is not, we might have a case like
               // found = java.lang.Integer, test = Int, which could be true
               // (not sure why that is so, but scalac behaves the same way)
            !isDerivedValueClass(foundCls) && !isDerivedValueClass(testCls)
               // we don't have the logic to handle derived value classes

          /** Check whether a runtime test that a value of `foundCls` can be a `testCls`
           *  can be true in some cases. Issure a warning or an error if that's not the case.
           */
          def checkSensical: Boolean =
            if (!isCheckable) true
            else if (foundCls.isPrimitiveValueClass && !testCls.isPrimitiveValueClass) {
                ctx.error("cannot test if value types are references", tree.pos)
                false
              }
            else if (!foundCls.derivesFrom(testCls)) {
              if (foundCls.is(Final)) {
                unreachable(i"$foundCls is not a subclass of $testCls")
                false
              }
              else if (!testCls.derivesFrom(foundCls) &&
                       (testCls.is(Final) ||
                        !testCls.is(Trait) && !foundCls.is(Trait))) {
                unreachable(i"$foundCls and $testCls are unrelated")
                false
              }
              else true
            }
            else true


          if (expr.tpe <:< testType)
            if (expr.tpe.isNotNull) {
              /* Do not warn the user if the original testType was a
               * qualified type, as it might not always yield true, depending
               * on wether the runtime checks on the qualifier pass or not */
              if(!wasQtype)
                ctx.warning(
                  em"this will always yield true, since `$foundCls` is a subclass of `$testCls`",
                  expr.pos)
              constant(expr, Literal(Constant(true)))
            }
            else expr.testNotNull
          else if (!checkSensical)
            constant(expr, Literal(Constant(false)))
          else if (testCls.isPrimitiveValueClass)
            if (foundCls.isPrimitiveValueClass)
              constant(expr, Literal(Constant(foundCls == testCls)))
            else
              transformIsInstanceOf(expr, defn.boxedType(testCls.typeRef), flagUnrelated)
          else
            derivedTree(expr, defn.Any_isInstanceOf, testType)
        }

        def transformAsInstanceOf(testType: Type): Tree = {
          def testCls = testType.widen.classSymbol
          val unerasedTestType = tree.args.head.tpe

          if(tree.args.head.tpe.isInstanceOf[QualifiedType] && !inMatch)
            ctx.warning(em"No dynamic checks are done on qualifiers using asInstanceOf. Please use a pattern match instead!", expr.pos)

          if (expr.tpe <:< testType)
            Typed(expr, tree.args.head)
          else if (foundCls.isPrimitiveValueClass) {
            if (testCls.isPrimitiveValueClass) primitiveConversion(expr, testCls)
            else derivedTree(box(expr), defn.Any_asInstanceOf, testType)
          }
          else if (testCls.isPrimitiveValueClass)
            unbox(expr.ensureConforms(defn.ObjectType), testType)
          else if (isDerivedValueClass(testCls)) {
            expr // adaptToType in Erasure will do the necessary type adaptation
          }
          else
            derivedTree(expr, defn.Any_asInstanceOf, testType)
        }

        /** Transform isInstanceOf OrType
         *
         *    expr.isInstanceOf[A | B]  ~~>  expr.isInstanceOf[A] | expr.isInstanceOf[B]
         *    expr.isInstanceOf[A & B]  ~~>  expr.isInstanceOf[A] & expr.isInstanceOf[B]
         *
         *  The transform happens before erasure of `testType`, thus cannot be merged
         *  with `transformIsInstanceOf`, which depends on erased type of `testType`.
         *
         *  Qualified type runtime checks for isInstanceOf are added here as once the
         *  types are erased, we loose the information about qualifications.
         *
         */
        def transformTypeTest(expr: Tree, testType: Type, flagUnrelated: Boolean): Tree = testType.dealias match {
          case _: SingletonType =>
            expr.isInstance(testType).withPos(tree.pos)
          case OrType(tp1, tp2) =>
            evalOnce(expr) { e =>
              transformTypeTest(e, tp1, flagUnrelated = false)
                .or(transformTypeTest(e, tp2, flagUnrelated = false))
            }
          case AndType(tp1, tp2) =>
            evalOnce(expr) { e =>
              transformTypeTest(e, tp1, flagUnrelated)
                .and(transformTypeTest(e, tp2, flagUnrelated))
            }
          case defn.MultiArrayOf(elem, ndims) if isUnboundedGeneric(elem) =>
            def isArrayTest(arg: Tree) =
              ref(defn.runtimeMethodRef(nme.isArray)).appliedTo(arg, Literal(Constant(ndims)))
            if (ndims == 1) isArrayTest(expr)
            else evalOnce(expr) { e =>
              derivedTree(e, defn.Any_isInstanceOf, e.tpe)
                .and(isArrayTest(e))
            }
          case qt: ComplexQType => {
            /* Simpler version of the function found in ElimPrecisePrimitives, because we may rebuild precise
             * primitives from the types inside QualifiedTypes and want to remove them before CGen happens */
            def transformSelect(tree: Select)(implicit ctx: Context): Tree = {
              import NameKinds.PrecisePrimName
              tree.tpe match {
                case tp: TermRef =>
                  tp.name match {
                    case PrecisePrimName(primName) =>
                      val prefix = tp.prefix
                      val newDenots = prefix.member(primName).atSignature(tp.signature, prefix).alternatives
                      assert(newDenots.size == 1)
                      val newDenot = newDenots.head
                      Select(tree.qualifier, primName).withType(prefix.select(primName, newDenot))
                    case _ =>
                      tree
                  }
                case _ =>
                  tree
              }
            }

            /* Takes a qualified type and an expression and returns a tree that will apply the type's
             * predicate on the expression.
             */
            def applyQTypePredicate(qt: ComplexQType, expr: Tree): Tree = {
              import qtyper.extraction.ConstraintExpr._
              def helper(tp: Type): Tree = tp match {
                case ConstantType(Constant(value)) => Literal(Constant(value))
                case qf: QualifierSubject => expr
                /* Two things are happening here: firstly a TermRef who's prefix is a QualifierSubject will be
                 * cause a match error in the `singleton` call of `ref`; therefore since it would've been
                 * exchanged with `expr` later in recursion, we replace it now. Secondly, the types used
                 * inside QualifiedTypes remain @precise, causing the backend to fail if we do not re-run some
                 * of the checks in the `elimPrecisePrimitives` here (as we are using the types to get the
                 * trees back). */
                case TermRef(qt: QualifierSubject, tDesig) => {
                  helper(TermRef(expr.tpe, tDesig)).withPos(expr.pos) match {
                    case t: Select => transformSelect(t)
                    case t => t
                  }
                }
                case tr: TermRef => ref(tr)

                case UnaryPrimitiveQType(_, prim, tp1) => {
                  val subject = helper(tp1)
                  prim match {
                    case Primitives.Not =>
                      subject.select(nme.UNARY_!).appliedTo(subject)
                    case Primitives.UMinus =>
                      subject.select(nme.MINUS).appliedTo(subject)
                    case _ => theEmptyTree
                  }
                }
                case bt @ BinaryPrimitiveQType(_, prim, tp1, tp2) => {
                  val arg = helper(tp2.widenSkolem)
                  val sig = Signature(resultType = defn.BooleanType, isJava = false).prepend(params = List(arg.tpe), isJava = false)
                  if(arg.isEmpty)
                    theEmptyTree
                  else {
                    prim match {
                      case Primitives.Equals =>
                        helper(tp1).selectWithSig(nme.EQ, sig).appliedTo(arg)
                      case Primitives.NotEquals =>
                        helper(tp1).selectWithSig(nme.NE, sig).appliedTo(arg)
                      case Primitives.And =>
                        helper(tp1).selectWithSig(nme.ZAND, sig).appliedTo(arg)
                      case Primitives.Or =>
                        helper(tp1).selectWithSig(nme.ZOR, sig).appliedTo(arg)
                      case Primitives.Plus =>
                        helper(tp1).selectWithSig(nme.PLUS, sig).appliedTo(arg)
                      case Primitives.Minus =>
                        helper(tp1).selectWithSig(nme.PLUS, sig).appliedTo(arg.select(nme.MINUS).appliedTo(arg))
                      case Primitives.Times =>
                        helper(tp1).selectWithSig(nme.MUL, sig).appliedTo(arg)
                      case Primitives.Division =>
                        helper(tp1).selectWithSig(nme.DIV, sig).appliedTo(arg)
                      case Primitives.Remainder =>
                        // There is no 'primitive name' for modulo, so we skip it for now
                        ctx.warning(em"Runtime checking of qualifiers containing the $prim primitive is not yet implemented")
                        theEmptyTree
                      case Primitives.LessThan =>
                        helper(tp1).selectWithSig(nme.LT, sig).appliedTo(arg)
                      case Primitives.GreaterThan =>
                        helper(tp1).selectWithSig(nme.GT, sig).appliedTo(arg)
                      case Primitives.LessEquals =>
                        helper(tp1).selectWithSig(nme.LE, sig).appliedTo(arg)
                      case Primitives.GreaterEquals =>
                        helper(tp1).selectWithSig(nme.GE, sig).appliedTo(arg)
                      case _ => theEmptyTree
                    }
                  }
                }
                case t =>
                  ctx.warning(em"I was unable to rebuild a predicate from the QualifiedType $t, therefore no runtime checks will be done here", expr.pos)
                  theEmptyTree
              }

              val qualifier = helper(qt.qualifierTp)
                if (qualifier.isEmpty) Literal(Constant(true)).withPos(expr.pos)  // We warn that there will be no runtime checks and let things fall through
                else qualifier                                                    // The qualifier will be checked.
            }
            // FIXME: Store expression's value in a temporary variable to avoid repeating side-effects.
            // Check the traditional isInstanceOf and iff it is true then our predicate. Avoid if true/false
            // then ... constructs by matching on the result.
            val tradTrans = transformIsInstanceOf(expr, erasure(testType), flagUnrelated, wasQtype = true)
            tradTrans match {
              case Literal(Constant(true)) => applyQTypePredicate(qt, expr)
              case f @ Literal(Constant(false)) => f
              case _ =>
                If(tradTrans,
                  applyQTypePredicate(qt, expr), // If original isInstanceOf is true, is predicate true ?
                  Literal(Constant(false))) // The original isInstanceOf is false, so qualifying it won't change that.
            }
          }

          case _ =>
            transformIsInstanceOf(expr, erasure(testType), flagUnrelated)
        }

        if (sym.isTypeTest) {
          transformTypeTest(expr, tree.args.head.tpe, flagUnrelated = true)
        }
        else if (sym eq defn.Any_asInstanceOf)
          transformAsInstanceOf(erasure(tree.args.head.tpe))
        else tree

      case _ =>
        tree
    }
  }
}
