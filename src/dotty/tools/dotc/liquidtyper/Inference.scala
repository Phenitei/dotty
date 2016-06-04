package dotty.tools.dotc
package liquidtyper

import config.Printers.ltypr
import core.Contexts.Context
import core.Decorators._
import util.Positions.Position

import Constraint.{WfConstraint, SubtypConstraint}
import Typing.QualVarInfo
import extraction.Extractor

import leon.solvers.Model
import leon.utils.Bijection

import scala.collection.Map
import scala.collection.mutable


abstract class Inference

object Inference {
  type QualId  = Identifier
  type QualMap = Map[QualId, Qualifier] // Values are really Qualifier.ExtractedExpr | Qualifier.Disj
  type QualEnv = Map[QualId, Set[TemplateEnv.Binding]]

  val qualIdTop   = FreshIdentifier("Top")
  val groundQuals = Bijection[Qualifier, QualId]() // Key is really ExtractedExpr | PendingSubst | Disj

  // XXX(Georg): Is it okay to return different QualIds for Qualifiers that are equivalent (but cannot be proven so)?
  object HasQualId {
    def unapply(qtp: QType): Option[(QType, QualId)] = qtp match {
      case _: QType.FunType =>
        None
      case QType.BaseType(_, Qualifier.Var(qualVarId)) =>
        Some((qtp, qualVarId))
      case QType.BaseType(_, qualifier) =>
        // FIXME(Georg): If qualifier == PendingSubst(Var(...), ...) we also get here. Should these be separate?
        val id = groundQuals.cachedB(qualifier) { FreshIdentifier("G", alwaysShowUniqueID = true) }
        Some((qtp, id))
      case _: QType.UninterpretedType =>
        // We could in principle return qualIdTop here, but since this will only give use lots of trivial constraints
        // later on, we omit it here.
        // TODO: Reconsider once we allow qualifiers on UninterpretedTypes
        None
    }
  }
}

/**
  * Precise liquid type inference.
  *
  * Phases:
  *   A. Decompose constraints and discard those trivially satisfied
  *   B. Eliminate all qualifier variables
  *     1) Replace qualifier variables by ascriptions, where present
  *     2) Create qualifier var implication graph and mark unsafe qualifier vars (that is, those coming from types of
  *       method parameters that have not been ascribed a qualifier)
  *     3) Merge equivalent qualifier vars
  *     4a) Compute precise qualifiers by topologically traversing yet-to-be-determined, safe qualifier vars
  *     4b) Assign trivial qualifier to those that cannot be determined precisely
  *   C. Send remaining constraints to SMT solver and return result
  */
class PreciseInference(typing: Typing)(implicit ctx: Context) extends Inference {

  import Inference._

  /** Helpers */

  private def unfoldSubtypConstraint(env: TemplateEnv, tpA: QType, tpB: QType, pos: Position, covariant: Boolean,
                                     acc: List[SubtypConstraint]): List[SubtypConstraint] = {
    tpA match {
      case funTpA @ QType.FunType(paramsA, resultA) =>
        val funTpB @ QType.FunType(paramsB, resultB) = tpB
        val acc1 = (acc /: (paramsA.values zip paramsB.values)) { case (acc_, (paramTpA, paramTpB)) =>
          unfoldSubtypConstraint(env, paramTpA, paramTpB, pos, !covariant, acc_)
        }
        // FIXME(Georg): We should match parameters from funTpB to the ones added in the resultEnv of funTpA here and
        //  then substitute funTpA's parameter names for their counterparts in funTpB.
        val resultEnv = funTpA.resultEnv(env)
        unfoldSubtypConstraint(resultEnv, resultA, resultB, pos, covariant, acc1)

      case _ if covariant   => SubtypConstraint(env, tpA, tpB, pos) :: acc
      case _ if !covariant  => SubtypConstraint(env, tpB, tpA, pos) :: acc
    }
  }

  private def computeQualIdEnv(constraints: List[WfConstraint]): QualEnv =
  {
    val qualIdEnv = new mutable.HashMap[QualId, Set[TemplateEnv.Binding]]()

    // Decomposes a potentially complex WfConstraint into multiple that are only over simple QTypes
    def unfold(env: TemplateEnv, tp: QType): Unit = tp match {
      case tpe @ QType.FunType(params, result) =>
        unfold(tpe.resultEnv(env), tpe.result)
        params.valuesIterator.foreach(unfold(env, _))
      case HasQualId(_, qualId) =>
        val oldBindings = env.bindings.valuesIterator.toSet
        val newBindings = qualIdEnv.get(qualId) match {
          case None     => oldBindings
          case Some(bs) => oldBindings intersect bs
        }
        qualIdEnv(qualId) = newBindings
      case _ =>
        // TODO(Georg): Also handle other QTypes
    }

    for (WfConstraint(env, tp, _) <- constraints)
      unfold(env, tp)
    qualIdEnv.asInstanceOf[Map[QualId, Set[TemplateEnv.Binding]]]
  }


  /** Inference phases */

  private def eliminateQualVars(qualEnv: QualEnv,
                                constraints: List[SubtypConstraint]): (QualMap, List[SubtypConstraint]) = {
    // Initialize the resulting qualifier variable map
    val qualMap         = new mutable.HashMap[QualId, Qualifier]()
    qualMap(qualIdTop)  = Qualifier.True
    val remainingCs     = new mutable.ArrayBuffer[SubtypConstraint]()

    def assigned        = qualMap.contains(_)
    def getAssignedOrGroundQual(id: QualId): Qualifier = qualMap.getOrElse(id, groundQuals.toA(id))

    val qualVarIds      = typing.qualVars.map(_.id)
//    val qualVars        = qualVarIds ++ OTHERS

    // 1. Replace by ascribed qualifiers and signatures, where present
    // FIXME(Georg): Should we actually use the env we have for each qualVar mapping?
    for ((Qualifier.Var(id), QualVarInfo(_, _, Some(expr), _)) <- typing.qualVarInfo) {
      val qual = Qualifier.ExtractedExpr(expr)
      assert(qual.freeVars subsetOf (qualEnv(id).map(_.identifier) union Extractor.subjectVarIds),
        "Ascribed qualifiers should by construction only capture variables in the environment.")
      qualMap(id) = qual
    }
//    val fixedQualVars = index.qualVarExpectation.keySet

    // 2. Create qualifier variable implication graph
    //  (K1 -> K2 expresses that qual var K1 is a subtype of qual var K2)
    val inEdges  = new mutable.HashMap[QualId, List[(TemplateEnv, QualId)]].withDefaultValue(List.empty)
    val outEdges = new mutable.HashMap[QualId, List[QualId]].withDefaultValue(List.empty)

    constraints foreach {
      case SubtypConstraint(env, HasQualId(_, idA), HasQualId(_, idB), _) =>
        inEdges(idB)        = env -> idA :: inEdges(idB)
        outEdges(idA)       = idB :: outEdges(idA)
      case SubtypConstraint(env, tpA, HasQualId(_, idB),_ ) =>
        inEdges(idB)        = env -> qualIdTop :: inEdges(idB)
        outEdges(qualIdTop) = idB :: outEdges(qualIdTop)
      case constraint =>
        // FIXME(Georg): Is it even possible to add any constraints here given that we will only be passed non-trivial
        //  SubtypConstraints?
        remainingCs        += constraint
    }

    // 3. Merge equivalent qualifier variables
    // XXX(Georg): Scrap equivalence classes for now?
    //  As far as I can tell, implication-cycles ("equivalences") should be impossible, if we disallow outgoing edges
    //  from qualifier variables originating from parameters (as we currently do).
//    // Equivalence classes for qualifier vars
//    val eqClass = mutable.Map[QualId, QualId]()
////    for (Qualifier.Var(id) <- index.qualVarIds)
////      eqClass(id) = id
//
//    def mergeEqQualVars(qualVar: QualId, path: List[QualId]): Unit = {
//      ???
//    }
//
//    index.qualVarIds.foreach { case Qualifier.Var(id) => mergeEqQualVars(id, List(id)) }

    // 4. Assign qualifier variables
    // "Safe" are those qualifier variables that we can be sure to know all constraints for
//    val unsafeQualVars = index.qualVarIds filter index.qualVarInParam map { _.id }
    val unsafeQualIds = typing.qualVarInfo.collect { case (Qualifier.Var(id), info) if info.inParam => id } .toSet
    val safeQualIds   = qualVarIds diff unsafeQualIds

    // Assign True to all unsafe qualifier vars that weren't ascribed a qualifier in the first place
    for (id <- unsafeQualIds if !qualMap.contains(id))
      qualMap(id) = Qualifier.True

    // Precisely capture qualifier vars where we can be sure to know of all subtyping constraints
    //  (We essentially do a topological sort to make sure all qualifier we rely on are already concrete)
//    val succsOfUnsafe = unsafeQualIds.flatMap(outEdges).toSeq
    val predLeft = {
      val pairs = inEdges map { case (id, edges) =>
//        id -> (edges count { case (_, from) => qualVarIds(from) && !unsafeQualIds(from) })
        id -> (edges count { case (_, from) => qualVarIds(from) && !assigned(from) })
      }
      mutable.HashMap(pairs.toSeq: _*)
    }
    val initialSources  = predLeft.collect { case (id, 0) if !assigned(id) => id } .toSeq
    val frontier        = mutable.Queue[QualId](initialSources: _*)
    val inferred        = mutable.Set[QualId]()

//    println(s"QualVarInfo:\n\t${typing.qualVarInfo}")
//    println(s"Unsafe qual ids: $unsafeQualIds")
//    println(s"outEdges:\n\t$outEdges")
//    println(s"predLeft: $predLeft")
//    println(s"initialSources: $initialSources")

    // FIXME: Do we still have to ignore unsafe qual ids here?
    while (frontier.nonEmpty) {
      val id     = frontier.dequeue()
      inferred  += id

      val incoming = inEdges(id)
      if (incoming.nonEmpty) {
        // TODO: Should really just add the additional path condition here rather than a seperate TemplateEnv
        val envQuals  = incoming map { case (incEnv, incId) => (incEnv, getAssignedOrGroundQual(incId)) }
        for ((incEnv, incQual) <- envQuals) assert(incQual.qualifierVars.isEmpty) // Sanity check
        qualMap(id)   = Qualifier.Disj(envQuals)
      }

      for (outId <- outEdges(id)) {
        val left = predLeft(outId) - 1
        predLeft(outId) = left
        if (!assigned(outId) && left == 0)
          frontier.enqueue(outId)
      }
    }

    // Add back constraints for qualifiers we didn't infer precisely
    val retainConstraintsTo = inEdges.keySet diff inferred
    for (c @ SubtypConstraint(_, _, HasQualId(_, idB), _) <- constraints if retainConstraintsTo(idB))
      remainingCs += c

    // Sanity checks
    for ((id, left) <- predLeft if safeQualIds(id) && left > 0)
      ctx.error(s"Qualifier variable elimination couldn't handle qual var $id -- appears to be part of cycle")
    for ((id, qual) <- qualMap if qual.qualifierVars.nonEmpty)
      throw new AssertionError(s"After qualifier variable elimination $id must not point to other qual vars: $qual")

    // Assign True to all remaining qualifier variables
    // XXX(Georg): This essentially means we don't have any constraints for a safe qualifier variable. Probably fishy.
    for (id <- qualVarIds diff qualMap.keySet) {
      ctx.warning(s"Qualifier variable $id seems to have no incoming constraints")
      qualMap(id) = Qualifier.True
    }

    // Check that each assignment we made doesn't violate the well-formedness constraints
    for ((id, availableBindings) <- qualEnv)
      if (!(qualMap(id).freeVars subsetOf (availableBindings.map(_.identifier) union Extractor.subjectVarIds))) {
        ctx.warning(s"Precise qualifier for qualifier var $id would not eliminate all parameters, falling back to True")
//        ltypr.println(s"qualMap($id) = ${qualMap(id)} // free vars: ${qualMap(id).freeVars} " +
//          s"// available bindings: $availableBindings")
        qualMap(id) = Qualifier.True
      }

    (qualMap.toMap, remainingCs.toList)
  }

  def apply(constraints: List[Constraint]): Boolean = {
    // Inv: \forall (k,v) \in qualMap : v contains no Qualifier.Var

    /** A. Decompose constraints over MethodTypes into constraints over base types only */

    def partitionByConstraintType(cs: List[Constraint]): (List[SubtypConstraint], List[WfConstraint]) = {
      val (cs1, cs2) = cs.partition(_.isInstanceOf[SubtypConstraint])
      (cs1.asInstanceOf[List[SubtypConstraint]], cs2.asInstanceOf[List[WfConstraint]])
    }
    val (subtypConstraints0, wfConstraints0) = partitionByConstraintType(constraints)

    // Extract SubtypConstraints that are non-trivial (not implied to hold by the soundeness of the Dotty typer) and
    // decompose them into constraints of base types (rather than complex types such as MethodType)
    val subtypConstraints = subtypConstraints0 flatMap {
      case SubtypConstraint(env, tpA, tpB, pos) =>
        val baseConstraints = unfoldSubtypConstraint(env, tpA, tpB, pos, covariant = true, List.empty).reverse
        // Get rid of SubtypConstraints that hold trivially due to the soundness of Dotty's Typer and decompose the rest
        baseConstraints filter {
          case SubtypConstraint(_, _, QType.BaseType(_, qualifier), _)  => qualifier ne Qualifier.True
          case _                                                        => false
        }
      case _ =>
        Seq.empty
    }

    // Extract the environments within which each qualifier var needs to eventually be well-formed
    val qualEnv = computeQualIdEnv(wfConstraints0)


    /** B. Eliminate all qualifier vars */

//    println(s"Constraints before eliminateQualVars:"); for (c <- subtypConstraints) println(i"\t$c")
    val (qualMap, remainingCs) = eliminateQualVars(qualEnv, subtypConstraints)
//    println(s"Constraints after eliminateQualVars:"); for (c <- remainingCs) println(i"\t$c")

    if (ctx.reporter.errorsReported)
      return false


    /** Debug output */

    def printQualVarMap(qualMap: QualMap, prefix: String = "") =
      ltypr.println(qualMap.toList.sortBy(_._1.toString)
        .map{ case (v,q) => i"$v: $q" }.mkString(prefix, "\n\t\t", ""))
    printQualVarMap(qualMap, prefix="\n\tQualifier map:\n\t\t")

    val consStr = remainingCs.map(_.show).mkString("\n\t\t")
    ltypr.println(s"\n\tRemaining constraints:\n\t\t$consStr")


    // C. Send remaining constraints to SMT solver and return result
    testConstraints(qualMap, remainingCs)
  }

  // TODO(Georg): Implement type inference via predicate abstraction

  protected def grounded(qualMap: QualMap, b: TemplateEnv.Binding): TemplateEnv.Binding =
    b.copy(templateTp = b.templateTp.substQualVars(qualMap))
  protected def grounded(qualMap: QualMap, e: TemplateEnv): TemplateEnv =
    e.copy(bindings = e.bindings.mapValues(grounded(qualMap, _)))
  protected def grounded(qualMap: QualMap, c: SubtypConstraint): SubtypConstraint =
    c.copy(env = grounded(qualMap, c.env), tpA = c.tpA.substQualVars(qualMap), tpB = c.tpB.substQualVars(qualMap))

  def testConstraints(qualMap: QualMap, constraints: Seq[SubtypConstraint])(implicit ctx: Context): Boolean = {
    def reportViolation(constraint: SubtypConstraint, model: Model): Unit = {
      val groundedC = grounded(qualMap, constraint)
      val modelStr = model.seq.map { case (id, expr) => s"$id: $expr" } .mkString("\n\t\t", "\n\t\t", "")
      ctx.error(i"constraint violation\n\t(abstract) $constraint\n\t(grounded) $groundedC\n\t" +
        i"Counterexample:$modelStr", constraint.pos)
    }

    val solver = Solver(qualMap, typing.unboundIds)
    for (constraint <- constraints) {
      solver.push()
      solver.assertSubtypConstraint(constraint)
      solver.check match {
        case None =>
          ctx.error(s"Could not solve constraint $constraint in solver.")
          return false

        case Some(true) =>
          reportViolation(constraint, solver.getModel)
          return false

        case Some(false) =>
          ctx.inform(i"Constraint $constraint is valid.")
      }
      solver.pop()
    }

    true
  }

}