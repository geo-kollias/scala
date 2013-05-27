package scala.tools.reflect.declosurify

import scala.collection.generic.FilterMonadic

class MacroSupport[C <: Ctx](final val c: C) extends ReflectionSupport {
  val u: c.universe.type = c.universe
  import u._

  def dumpContext(): Unit = System.err.println(
    s"""
      macroApplication   =${c.macroApplication}
      enclosingMacros    =${c.enclosingMacros}
      enclosingImplicits =${c.enclosingImplicits}
      enclosingPosition  =${c.enclosingPosition}
      enclosingMethod    =${c.enclosingMethod}
      enclosingClass     =${c.enclosingClass}
      enclosingUnit      =${c.enclosingUnit}
      enclosingRun       =${/*c.enclosingRun*/ "run" }
    """
  )

  def freshName(prefix: String): TermName = newTermName(c.fresh(prefix))
  def enclClass: ClassSymbol = c.enclosingClass.symbol match {
    case x: ModuleSymbol => x.moduleClass.asClass
    case x: ClassSymbol  => x
  }
  def enclMethod = c.enclosingMethod match {
    case null   =>
      c.warning(c.enclosingPosition, s"enclosingMethod is null, using $enclClass instead.")
      dumpContext()
      enclClass
    case m      => m.symbol
  }

  private def logging = sys.props contains "declosurify.debug"


  def log(msg: String) = if (logging) Console.err.println(msg)
  def log_?[T](value: T)(pf: PartialFunction[T, Any]): T = {
    if (pf isDefinedAt value)
      log("" + pf(value))

    value
  }

  private def isMacroOpsImplicit(method: Symbol) = log_?(
       method.producedType.isDefinedWithAnnotation[macroExtension]
    && (method.producedType member 'xs) != NoSymbol
  ) {
    case false =>
      ((method.producedType, method.producedType.isDefinedWithAnnotation[macroExtension], method.producedType member 'xs))
  }

  lazy val collectionType: Type = {
    val retCollectionType = Some(c.prefix.actualType)
    retCollectionType
  }
  lazy val elementType: Type    = Some(c.prefix.actualType.typeArgs) collect { case elem :: _ :: Nil => elem }

  object ArrayPrefix {
    def unapply[T](prefix: c.Expr[T]): Option[Tree] = {
      if (collectionType.isArrayType) Some(prefixCollectionTree) else None
    }
  }
  object ArrayOpsPrefix {
    def unapply[T](prefix: c.Expr[T]): Option[Tree] = {
      if (collectionType.isArrayOpsType) Some(prefixCollectionTree) else None
    }
  }
  object LinearPrefix {
    def unapply[T](prefix: c.Expr[T]): Option[Tree] = {
      if (collectionType.isLinearSeqType) Some(prefixCollectionTree) else None
    }
  }
  object ImmutIndexedPrefix {
    def unapply[T](prefix: c.Expr[T]): Option[Tree] = {
      if (collectionType.isImmutIndexedSeqType) Some(prefixCollectionTree) else None
    }
  }
  object MutIndexedPrefix {
    def unapply[T](prefix: c.Expr[T]): Option[Tree] = {
      if (collectionType.isMutIndexedSeqType) Some(prefixCollectionTree) else None
    }
  }
  object TraversablePrefix {
    def unapply[T](prefix: c.Expr[T]): Option[Tree] = {
      if (collectionType.isTraversableType) Some(prefixCollectionTree) else None
    }
  }

  def prefixCollection[Coll1] = c.Expr[Coll1](prefixCollectionTree)

  def prefixCollectionTree = {
    val m = methPart(c.prefix.tree)
    println(s"""
        |   pre: $m
        |actual: ${c.prefix.actualType}
        |static: ${c.prefix.staticType}
        | first: ${m.tpe}
      """.stripMargin.trim
    )
    c.prefix.tree match {
      case Apply(sel, arg :: Nil) if isMacroOpsImplicit(sel.symbol) => arg
      case _                                                         => c.prefix.tree
    }
  }
  implicit def scalaSymbolToInvokeOps(x: scala.Symbol): InvokeOps = treeToInvokeOps(Ident(x.name: TermName))
  implicit def reflectSymbolToInvokeOps(x: Symbol): InvokeOps     = treeToInvokeOps(Ident(x))
  implicit def treeToInvokeOps(x: Tree): InvokeOps                = new InvokeOps(x)
  implicit def lowerInvokeOps(ops: InvokeOps): Tree               = ops.lhs

  class InvokeOps(val lhs: Tree) {
    def dot(name: scala.Symbol): InvokeOps = dot(name: TermName)
    def dot(name: Name): InvokeOps         = new InvokeOps(Select(lhs, name))
    def apply(args: Tree*): Tree           = Apply(lhs, args.toList)
    def apply[T1: c.WeakTypeTag] : Tree    = TypeApply(lhs, List(weakTypeOf[T1]) map (t => TypeTree(t)))
    def apply(t1: Type) : Tree             = TypeApply(lhs, List(t1) map (t => TypeTree(t)))
  }

  def newLocalMethod(name: TermName, vparams: List[ValDef], resultType: Type): MethodSymbol = {
    import build._
    val ddef = newNestedSymbol(enclMethod, name, enclMethod.pos, Flag.PRIVATE | METHOD, isClass = false)
    val params = vparams map { vd =>
      val sym = newNestedSymbol(ddef, vd.name, ddef.pos, Flag.PARAM, isClass = false)
      setTypeSignature(sym, vd.tpt.tpe)
      vd setSymbol sym
      sym
    }
    setTypeSignature(ddef, MethodType(params, resultType)).asMethod
  }

  def functionToLocalMethod(fnTree: Function): DefDef = {
    val Function(fparams, fbody) = fnTree
    val frestpe = fbody.tpe
    val fsyms   = fparams map (_.symbol)
    val vparams = for (vd @ ValDef(mods, name, tpt, _) <- fparams) yield ValDef(mods, name, TypeTree(vd.symbol.typeSignature.normalize), EmptyTree)
    val method  = newLocalMethod(freshName("local"), vparams, frestpe)
    val tree    = DefDef(NoMods, freshName("local"), Nil, List(vparams), TypeTree(frestpe), c.resetAllAttrs(fbody.duplicate))

    tree setSymbol method
    c.resetAllAttrs(tree)
    c.typeCheck(tree).asInstanceOf[DefDef]
  }
}

object MacroUtil {
  def showUs[T](a: T): T = macro showUsImpl[T]
  def showUsImpl[T](c: Ctx)(a: c.Expr[T]) = {
//    Console.err.println(c.universe.show(a.tree))
    System.err.println("showUs: " + c.universe.show(a.tree))
    a
  }
}