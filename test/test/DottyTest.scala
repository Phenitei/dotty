package test

import dotty.tools.dotc.core._
import dotty.tools.dotc.core.Contexts._
import dotty.tools.dotc.core.Symbols._
import dotty.tools.dotc.core.Flags._
import Types._, Symbols._, Decorators._
import dotty.tools.dotc.printing.Texts._
import dotty.tools.dotc.reporting.ConsoleReporter
import dotty.tools.dotc.core.Decorators._
import dotty.tools.dotc.ast.tpd
import dotty.tools.dotc.Compiler

import dotty.tools.dotc
import dotty.tools.dotc.core.Phases.Phase

class DottyTest /*extends ContextEscapeDetection*/ {

  dotty.tools.dotc.parsing.Scanners // initialize keywords

  implicit var ctx: Contexts.Context = {
    val base = new ContextBase
    import base.settings._
    val ctx = base.initialCtx.fresh
    base.initialize()(ctx)
    ctx
  }
/*
  override def getCtx: Context = ctx
  override def clearCtx() = {
    ctx = null
  }
*/
  type Assertion = (tpd.Tree, Context) => Unit

  protected def compilerWithChecker(phase: String)(assertionAfter: Assertion,
                                                   assertionBeforeOpt: Option[Assertion] = None) =
    new Compiler {
      override def phases = {
        val allPhases = super.phases
        val targetPhase = allPhases.flatten.find(p => p.phaseName == phase).get
        val groupsBefore = allPhases.takeWhile(x => !x.contains(targetPhase))
        val lastGroup = allPhases.find(x => x.contains(targetPhase)).get.takeWhile(x => !(x eq targetPhase))
        def assertionPhase(name: String, f: (tpd.Tree, Context) => Unit): Phase =
          new Phase {
            def phaseName = s"assertionChecker$name"
            override def run(implicit ctx: Context): Unit = f(ctx.compilationUnit.tpdTree, ctx)
          }
        val lastGroupsAppended = assertionBeforeOpt match {
          case Some(f)  => List(lastGroup, assertionPhase("before", f) :: Nil, targetPhase :: Nil)
          case None     => List(lastGroup ::: targetPhase :: Nil)
        }

        groupsBefore ::: lastGroupsAppended ::: List(List(assertionPhase("after", assertionAfter)))
      }
    }

  def checkCompile(checkAfterPhase: String, source: String)(assertion: (tpd.Tree, Context) => Unit): Unit = {
    val c = compilerWithChecker(checkAfterPhase)(assertion)
    c.rootContext(ctx)
    val run = c.newRun
    run.compile(source)
  }

  def checkCompile(checkAfterPhase: String, sources:List[String])(assertion:(tpd.Tree, Context) => Unit): Unit = {
    val c = compilerWithChecker(checkAfterPhase)(assertion)
    c.rootContext(ctx)
    val run = c.newRun
    run.compile(sources)
  }

  def methType(names: String*)(paramTypes: Type*)(resultType: Type = defn.UnitType) =
    MethodType(names.toList map (_.toTermName), paramTypes.toList, resultType)
}
