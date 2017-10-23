package dotty.tools.dotc
package qtyper.extraction

import dotty.tools.sharable
import core.Contexts._
import core.Decorators._
import core.Types._
import core.Symbols.{ClassSymbol, Symbol}

import stainless.{trees => st}
import st.{Expr, Variable}

import ConstraintExpr.{UnaryPrimitive, BinaryPrimitive}


/*
  When referring to another type on the logical level we need to make sure that we
  have a proper name to refer to it.
  The following class expresses *Dep*endencies of ConstraintExprs and ensures that within a
  cexpr we have a proper name, i.e., stainless variable, for each dependency.

  Consider SingletonTypes, for which we either have an explicit binding on the Dotty level or
  the SingletonType can be described locally, such as with constants.

  We call the former *external* dependencies, since they may be shared across multiple
  subexpressions.  Concretely, these arise from TermRefs and TermParamsRefs.
  We postulate the corresponding constraints once on the top-level of the VC.
  As a consequence, for external dependencies we simply keep subject variables around and
  don't freshen anything.

  For other types, e.g., those with more than one inhabitant, we need to be more careful.
  We call such dependencies *internal*.  When relying on an internal dependency, we must
  usually freshen all (internal) names that dependency relies on, including its subject
  variable.
  Similarly, we treat ConstantTypes and SkolemTypes as internal dependencies, with the notable
  optimizations that ConstantTypes always have an explicit form (`valExpr`) and SkolemTypes
  do not require freshening of their subject variable, since SkolemTypes are always fresh.
 */
sealed trait Dep {
  val tp: Type
  val subject: Variable

  /*
    Fresh Left(cExpr.valExpr.get, cExpr.scopeExpr) if tp.cExpr.valExpr.isDefined
    otherwise Right(cExpr.subject, cExpr.expr)
   */
  final def freshExprs(optSubst: Option[Map[Variable, Variable]] = None)(
    implicit ctx: Context): Either[(Expr, Expr), (Variable, Expr)] =
  {
    val cExpr = tp.cExpr
    //    println(i"XXX freshenedExpr($tp)  //  ${tp.toString}")
    //    println(s"ooo => $optSubst")
    val subst = optSubst.getOrElse {
      this match {
        case ExtDep(_) => Dep.freshSubst(cExpr.deps)
        case IntDep(_) => Dep.freshSubst(cExpr.deps) + (cExpr.subject -> subject)
      }
    }
    def substitute(e: Expr): Expr = st.exprOps.replaceFromSymbols(subst, e)

    cExpr.valExpr match {
      case Some(e) => Left(substitute(e) -> substitute(cExpr.scopeExpr))
      case None    => Right(substitute(cExpr.subject).asInstanceOf[Variable] -> substitute(cExpr.expr))
    }
  }

  final def freshExprsFlat()(implicit ctx: Context): (Expr, Expr) =
    freshExprs() match {
      case Left((e1, e2))  => (e1, e2)
      case Right((v1, e2)) => (v1, e2)
    }
}

final case class ExtDep(tp: Type)(implicit ctx: Context) extends Dep {
  val subject: Variable = tp.cExpr.subject
}
final case class IntDep(tp: Type)(implicit ctx: Context) extends Dep {
  val subject: Variable = tp.cExpr.subject.freshen
  @inline def substPair: (Variable, Variable) = tp.cExpr.subject -> subject
}

object Dep {
  def apply(tp: Type)(implicit ctx: Context): Dep =
    if (isExternal(tp)) ExtDep(tp) else IntDep(tp)

  def isExternal(tp: Type): Boolean = tp match {
    case _: TermRef | _: TermParamRef | _: QualifierSubject => true
    case _                                                  => false
  }

  def freshSubst(deps: Set[Dep]): Map[Variable, Variable] =
    deps.collect { case dep: IntDep => dep.substPair } .toMap
}


sealed trait ConstraintExpr {
  final protected type OptExpr = Option[Expr]

  def subject(implicit ctx: Context): Variable

  def scopeExpr(implicit ctx: Context): Expr /* Inv: subject does *not* occur in scopeExpr */
  def valExpr(implicit ctx: Context): OptExpr
  def propExpr(implicit ctx: Context): Expr
  def expr(implicit ctx: Context): Expr      /* Inv: expr == st.and(scopeExpr, *an expr constraining `subject`*) */

  def scope(implicit ctx: Context): Set[Dep] // types we directly depend on
  def deps(implicit ctx: Context): Set[Dep]  // types we transitively depend on


  type ThisCExpr >: Null <: ConstraintExpr { type ThisCExpr <: ConstraintExpr.this.ThisCExpr }

  def mapScope(f: Type => Type)(implicit ctx: Context): ThisCExpr

  def subst(from: BindingType, to: BindingType)(implicit ctx: Context): ThisCExpr =
    mapScope(_.subst(from, to))

  def subst(from: List[Symbol], to: List[Type])(implicit ctx: Context): ThisCExpr =
    mapScope(_.subst(from, to))

  def substDealias(from: List[Symbol], to: List[Type])(implicit ctx: Context): ThisCExpr =
    mapScope(_.substDealias(from, to))

  def substSym(from: List[Symbol], to: List[Symbol])(implicit ctx: Context): ThisCExpr =
    mapScope(_.substSym(from, to))

  def substThis(from: ClassSymbol, to: Type)(implicit ctx: Context): ThisCExpr =
    mapScope(_.substThis(from, to))

  def substRecThis(from: RecType, to: Type)(implicit ctx: Context): ThisCExpr =
    mapScope(_.substRecThis(from, to))

  def substParam(from: ParamRef, to: Type)(implicit ctx: Context): ThisCExpr =
    mapScope(_.substParam(from, to))

  def substParams(from: BindingType, to: List[Type])(implicit ctx: Context): ThisCExpr =
    mapScope(_.substParams(from, to))


  def exprStr(implicit ctx: Context): String
}

protected trait EmptyScope { self: ConstraintExpr =>
  final def scope(implicit ctx: Context): Set[Dep] = Set.empty[Dep]
  final def deps(implicit ctx: Context): Set[Dep]  = Set.empty[Dep]

  final def mapScope(f: Type => Type)(implicit ctx: Context): this.type = this
}

protected trait LazyExprsAndDeps { self: ConstraintExpr =>
  protected def init()(implicit ctx: Context): Unit

  protected[this] var myScopeExpr: Expr = _
  protected[this] var myValExpr: OptExpr = _
  protected[this] var myPropExpr: Expr = _
  protected[this] var myExpr: Expr = _

  final def scopeExpr(implicit ctx: Context): Expr   = { if (myScopeExpr == null) { init() }; myScopeExpr }
  final def valExpr(implicit ctx: Context): OptExpr  = { if (myValExpr == null) { init() }; myValExpr }
  final def propExpr(implicit ctx: Context): Expr    = { if (myPropExpr == null) { init() }; myPropExpr }
  final def expr(implicit ctx: Context): Expr        = { if (myExpr == null) { init() }; myExpr }

  protected[this] var myScope: Set[Dep] = _
  protected[this] var myDeps: Set[Dep] = _

  final def scope(implicit ctx: Context): Set[Dep] = { if (myScope == null) { init() }; myScope }

  final def deps(implicit ctx: Context): Set[Dep] = {
    if (myDeps == null)
      myDeps = scope.foldLeft(scope) { (deps0, dep) => deps0 union dep.tp.cExpr.deps }
    myDeps
  }
}


final case class TrivialCExpr(_subject: Variable)
  extends ConstraintExpr with EmptyScope
{
  def subject(implicit ctx: Context) = _subject

  def scopeExpr(implicit ctx: Context): Expr   = TrueLit
  def valExpr(implicit ctx: Context): OptExpr  = None
  def propExpr(implicit ctx: Context): Expr    = TrueLit
  def expr(implicit ctx: Context): Expr        = TrueLit

  type ThisCExpr = TrivialCExpr

  def exprStr(implicit ctx: Context): String = "true"
}


final case class ConstantCExpr(_subject: Variable, lit: st.Literal[_])
  extends ConstraintExpr with EmptyScope
{
  def subject(implicit ctx: Context) = _subject

  def scopeExpr(implicit ctx: Context): Expr   = TrueLit
  def valExpr(implicit ctx: Context): OptExpr  = Some(lit)
  def propExpr(implicit ctx: Context): Expr    = st.Equals(subject, lit)
  def expr(implicit ctx: Context): Expr        = propExpr

  type ThisCExpr = ConstantCExpr

  def exprStr(implicit ctx: Context): String = lit.toString
}


final case class RefCExpr(_subject: Variable)
  extends ConstraintExpr with EmptyScope
{
  def subject(implicit ctx: Context) = _subject

  // TermRefs etc. don't explicitly include their dependency's constraint expression (but expose it separately)
  def scopeExpr(implicit ctx: Context): Expr   = TrueLit
  def valExpr(implicit ctx: Context): OptExpr  = Some(subject)
  def propExpr(implicit ctx: Context): Expr    = TrueLit
  def expr(implicit ctx: Context): Expr        = TrueLit

  type ThisCExpr = RefCExpr

  def exprStr(implicit ctx: Context): String = subject.toString
}


final case class SkolemCExpr(tp: Type)
  extends ConstraintExpr with LazyExprsAndDeps
{
  private var myDep: Dep = _

  def subject(implicit ctx: Context) = { if (myDep == null) { init() }; myDep.subject }

  protected[this] def init()(implicit ctx: Context): Unit = {
    myDep = Dep(tp)
    myScope = Set(myDep)

    val (val1, scope1) = myDep.freshExprsFlat()
    myScopeExpr = scope1
    myValExpr   = Some(val1)
    myPropExpr  = st.Equals(subject, myValExpr.get)
    myExpr      = st.and(myScopeExpr, myPropExpr)
  }

  type ThisCExpr = SkolemCExpr
  def mapScope(f: Type => Type)(implicit ctx: Context): ThisCExpr = {
    val tp1 = f(tp)
    if (tp != tp1) SkolemCExpr(tp1) else this
  }

  def exprStr(implicit ctx: Context): String = expr.toString
}


trait PrimitiveCExpr extends ConstraintExpr {
  type ThisCExpr >: Null <: PrimitiveCExpr { type ThisCExpr <: PrimitiveCExpr.this.ThisCExpr }
}


final case class UnaryPrimitiveCExpr(_subject: Variable, tp1: Type, prim: UnaryPrimitive)
  extends PrimitiveCExpr with LazyExprsAndDeps
{
  private var myDep1: Dep = _

  def subject(implicit ctx: Context) = _subject

  protected[this] def init()(implicit ctx: Context): Unit = {
    myDep1 = Dep(tp1)
    myScope = Set(myDep1)

    val (val1, scope1) = myDep1.freshExprsFlat()
    myScopeExpr = scope1
    myValExpr   = Some(prim.builder(val1))
    myPropExpr  = st.Equals(subject, myValExpr.get)
    myExpr      = st.and(myScopeExpr, myPropExpr)
  }

  type ThisCExpr = UnaryPrimitiveCExpr
  def mapScope(f: Type => Type)(implicit ctx: Context): ThisCExpr = {
    val tp11 = f(tp1)
    if (tp1 != tp11) UnaryPrimitiveCExpr(subject, tp11, prim) else this
  }

  def exprStr(implicit ctx: Context): String = expr.toString()
}


final case class BinaryPrimitiveCExpr(_subject: Variable, tp1: Type, tp2: Type, prim: BinaryPrimitive)
  extends PrimitiveCExpr with LazyExprsAndDeps
{
  private var myDep1: Dep = _
  private var myDep2: Dep = _

  def subject(implicit ctx: Context) = _subject

  protected[this] def init()(implicit ctx: Context): Unit = {
    myDep1 = Dep(tp1)
    myDep2 = Dep(tp2)
    myScope = Set(myDep1, myDep2)

    val (val1, scope1) = myDep1.freshExprsFlat()
    val (val2, scope2) = myDep2.freshExprsFlat()
    myScopeExpr = st.and(scope1, scope2)
    myValExpr   = Some(prim.builder(val1, val2))
    myPropExpr  = st.Equals(subject, myValExpr.get)
    myExpr      = st.and(myScopeExpr, myPropExpr)
  }

  type ThisCExpr = BinaryPrimitiveCExpr
  def mapScope(f: Type => Type)(implicit ctx: Context): ThisCExpr = {
    val tp11 = f(tp1)
    val tp21 = f(tp2)
    if (tp1 != tp11 || tp2 != tp21) BinaryPrimitiveCExpr(subject, tp11, tp21, prim) else this
  }

  def exprStr(implicit ctx: Context): String = expr.toString()
}


final case class ComplexCExpr(_subject: Variable, subjectTp: QualifierSubject, qualifierTp: Type)
  extends ConstraintExpr with LazyExprsAndDeps
{
  private var mySubjectDep: Dep = _
  private var myQualifierDep: Dep = _

  def subject(implicit ctx: Context) = _subject

  protected[this] def init()(implicit ctx: Context): Unit = {
    // NOTE: Potentially creating an IntDep with a fresh subject is a bit funky, since we'll never use it!
    mySubjectDep   = Dep(subjectTp)
    myQualifierDep = Dep(qualifierTp)
    myScope        = Set(mySubjectDep, myQualifierDep)

    val cExprS = subjectTp.cExpr
    val cExprQ = qualifierTp.cExpr  // Inv: qualTp.widenDealias == BooleanType

    val subst = Dep.freshSubst(cExprS.deps union cExprQ.deps) + (cExprS.subject -> subject)
    val exprP = st.exprOps.replaceFromSymbols(subst, cExprS.expr)

    myQualifierDep.freshExprs(Some(subst)) match {
      case Left((valQ, scopeQ)) =>
        myScopeExpr = st.and(exprP, scopeQ)
        myPropExpr  = valQ

      case Right((subjectQ, exprQ)) =>
        myScopeExpr = st.and(exprP, exprQ)
        myPropExpr  = subjectQ
    }

    myValExpr = None  // In general we have no explicit form for our subject variable
    myExpr    = st.and(myScopeExpr, myPropExpr)
  }

  type ThisCExpr = ComplexCExpr
  def mapScope(f: Type => Type)(implicit ctx: Context): ThisCExpr = {
    val subjectTp1   = f(subjectTp).asInstanceOf[QualifierSubject]
    val qualifierTp1 = f(qualifierTp)
    if (subjectTp != subjectTp1 || qualifierTp != qualifierTp1) ComplexCExpr(subject, subjectTp1, qualifierTp1)
    else this
  }

  def exprStr(implicit ctx: Context): String = qualifierTp.cExpr.subject.toString() //expr.toString()
}


object ConstraintExpr {
  def depSubjectMap(tp: Type)(implicit ctx: Context): Map[Variable, Type] = {
    val cExpr = tp.cExpr
    val depSubjectMap0: Map[Variable, Type] = cExpr.deps.map(dep => dep.subject -> dep.tp).toMap
    depSubjectMap0 + (cExpr.subject -> tp)
  }

  sealed trait Primitive { val id: Int }
  final case class UnaryPrimitive(id: Int, builder: (Expr) => Expr) extends Primitive
  final case class BinaryPrimitive(id: Int, builder: (Expr, Expr) => Expr) extends Primitive

  object Primitives {
    import scala.collection.mutable.{Map => MutableMap}

    private val idMap = MutableMap.empty[Int, Primitive]

    private def unary(builder: (Expr) => Expr): UnaryPrimitive = {
      val prim = UnaryPrimitive(nextId, builder)
      idMap(nextId) = prim
      nextId += 1
      prim
    }

    private def binary(builder: (Expr, Expr) => Expr): BinaryPrimitive = {
      val prim = BinaryPrimitive(nextId, builder)
      idMap(nextId) = prim
      nextId += 1
      prim
    }

    def apply(id: Int): Primitive = idMap(id)

    private var nextId: Int = 1

    val Equals    = binary(st.Equals)
    val NotEquals = binary((a: Expr, b: Expr) => st.Not(st.Equals(a, b)))
    val Not       = unary(st.Not)
    val And       = binary((a: Expr, b: Expr) => st.And(a, b))
    val Or        = binary((a: Expr, b: Expr) => st.Or(a, b))

    val UMinus    = unary(st.UMinus)
    val Plus      = binary(st.Plus)
    val Minus     = binary(st.Minus)
    val Times     = binary(st.Times)
    val Division  = binary(st.Division)
    val Remainder = binary(st.Remainder)

    val LessThan      = binary(st.LessThan)
    val GreaterThan   = binary(st.GreaterThan)
    val LessEquals    = binary(st.LessEquals)
    val GreaterEquals = binary(st.GreaterEquals)

    val BVNot         = unary(st.BVNot)
    val BVAnd         = binary(st.BVAnd)
    val BVOr          = binary(st.BVOr)
    val BVXor         = binary(st.BVXor)
    val BVShiftLeft   = binary(st.BVShiftLeft)
    val BVAShiftRight = binary(st.BVAShiftRight)
    val BVLShiftRight = binary(st.BVLShiftRight)
  }


  def prettyPrintExpr(tp: QualifiedType, useValExpr: Boolean = false)(implicit ctx: Context): String = {
    val cExpr   = tp.cExpr
    val varOccs = new collection.mutable.ListMap[Variable, Int]
    val varTps  = ConstraintExpr.depSubjectMap(tp)
    val expr    = if (useValExpr) cExpr.valExpr.get else cExpr.expr
    val subject = cExpr.subject

    stainless.trees.exprOps.preTraversal {
      case v: Variable => varOccs(v) = varOccs.getOrElse(v, 0) + 1
      case _ => //
    } (expr)

    {
      object printer extends stainless.ast.Printer {
        val trees: st.type = st

        override protected def ppBody(tree: trees.Tree)(implicit pctx: st.PrinterContext): Unit = tree match {
          case v: trees.Variable if v == subject =>
            p"${v.id}"
          case v: trees.Variable =>
            varTps.get(v) match {
//              case Some(tp) =>  // TODO: Temporarily hiding imprecise types
              case Some(tp) if Dep.isExternal(tp) =>
                varOccs.get(v) match {
                  case Some(n) =>
                    varOccs -= v
//                    if (n == 1) p"⟦${tp.show}⟧"
//                    else        p"(${v.id}: ${tp.show})"
                    p"(${v.id}: ${tp.show})"
                  case None => p"${v.id}"
                }
              case _ =>
                // TODO(gsps): We miss some var -> tp mappings here because variables which have been
                //  freshened in Dep#freshExprs are not reflected in depSubjectMap.
//                p"!${v.id}@${v.id.globalId}!"
                p"${v.id}"
            }
          case _ => super.ppBody(tree)
        }
      }

      val opts = st.PrinterOptions()
      val pctx = st.PrinterContext(expr, Nil, opts.baseIndent, opts)
      printer.pp(expr)(pctx)
      pctx.sb.toString
    }
  }
}
