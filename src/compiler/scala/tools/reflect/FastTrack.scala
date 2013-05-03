package scala.tools
package reflect

import scala.reflect.reify.Taggers
import scala.tools.nsc.typechecker.{Analyzer, Macros}

/** Optimizes system macro expansions by hardwiring them directly to their implementations
 *  bypassing standard reflective load and invoke to avoid the overhead of Java/Scala reflection.
 */
trait FastTrack {
  self: Macros with Analyzer =>

  import global._
  import definitions._

  import scala.language.implicitConversions
  private implicit def context2taggers(c0: MacroContext): Taggers { val c: c0.type } = new { val c: c0.type = c0 } with Taggers
  private implicit def context2macroimplementations(c0: MacroContext): MacroImplementations { val c: c0.type } = new { val c: c0.type = c0 } with MacroImplementations

  implicit def fastTrackEntry2MacroRuntime(entry: FastTrackEntry): MacroRuntime = args => entry.run(args.c)
  type FastTrackExpander = PartialFunction[(MacroContext, Tree), Tree]
  case class FastTrackEntry(sym: Symbol, expander: FastTrackExpander) {
    def validate(c: MacroContext): Boolean = {
      println(showRaw(c.expandee))
      expander.isDefinedAt((c, c.expandee))
    }
    def run(c: MacroContext): Any = {
      val result = expander((c, c.expandee))
      c.Expr[Nothing](result)(c.WeakTypeTag.Nothing)
    }
  }

  lazy val fastTrack: Map[Symbol, FastTrackEntry] = {
    var registry = Map[Symbol, FastTrackEntry]()
    implicit class BindTo(sym: Symbol) { def bindTo(expander: FastTrackExpander): Unit = if (sym != NoSymbol) registry += sym -> FastTrackEntry(sym, expander) }
    materializeClassTag bindTo { case (c, Apply(TypeApply(_, List(tt)), List())) => c.materializeClassTag(tt.tpe) }
    materializeWeakTypeTag bindTo { case (c, Apply(TypeApply(_, List(tt)), List(u))) => c.materializeTypeTag(u, EmptyTree, tt.tpe, concrete = false) }
    materializeTypeTag bindTo { case (c, Apply(TypeApply(_, List(tt)), List(u))) => c.materializeTypeTag(u, EmptyTree, tt.tpe, concrete = true) }
    ApiUniverseReify bindTo { case (c, Apply(TypeApply(_, List(tt)), List(expr))) => c.materializeExpr(c.prefix.tree, EmptyTree, expr) }
    ReflectRuntimeCurrentMirror bindTo { case (c, _) => scala.reflect.runtime.Macros.currentMirror(c).tree }
    StringContext_f bindTo { case (c, app@Apply(Select(Apply(_, parts), _), args)) => c.macro_StringInterpolation_f(parts, args, app.pos) }
    TraversableLike_map bindTo { 
      // TODO(geokollias): r.macroMap({stats; x => x + 1}) is not matched properly
      case (c, app@Apply(Apply(TypeApply(Select(prefix, _), List(outElemTT, outCollTT)), List(f1@Function(List(ValDef(_, _, inElemTT, _)), expr))), List(bf))) => {
        c.macro_TraversableLike_macroMap(f1, inElemTT.tpe, expr.tpe, prefix.tpe, outCollTT.tpe, bf)
      }
    }
//    TraversableLike_map bindTo { case (c, app@Apply(TypeApply(Select(prefix, _), List(tt)), List(expr))) => c.macro_TraversableLike_macroMap[Int, Int, List[Int], List[Int]](expr, tt.tpe, app.pos) }
//    def mapInfix[A: c0.WeakTypeTag, B: c0.WeakTypeTag, Coll: c0.WeakTypeTag, That: c0.WeakTypeTag](c0: Ctx)(f0: c0.Expr[A => B]): c0.Expr[That]
//    List_macroMap bindTo { case (c, app@Apply(Select(Apply(_, parts), _), args)) => c.macro_List_macroMap(parts, args, app.pos) }
    registry
  }
}
