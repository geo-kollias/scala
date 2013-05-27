package scala.tools.reflect.declosurify

object Declosurify {
  def mapInfix[A, B](c0: Ctx)(f0: c0.Expr[A => B], inElemTpe: c0.Type, outElemTpe: c0.Type, inCollTpe: c0.Type, outCollTpe: c0.Type, bfTree: c0.Tree): c0.Tree = {
    val ctx = new MacroSupport[c0.type](c0)
    import ctx._
    import c.universe._
    
//    call.log[A, B]("f0" -> f0.tree)   // only for debugging purposes

    def isForeach = outCollTpe =:= typeOf[Unit]
    def mkFallbackImpl: c.Tree = {
      val name: TermName = if (isForeach) "foreachImpl" else "map"
      val pre = c.prefix.tree

      val fallbacktree = Apply(Select(pre, name), f0.tree :: Nil)
      fallbacktree
    }

    val flatStats = flatten(f0.tree)
    val fnTree = flatStats.reverse match {
      case (f: Function) :: _ => f
      case _                  => null
    }
    val useFallback = (
         ( fnTree == null)
      || ( c.enclosingMethod == null )
      || ( fnTree exists { case Return(_) => true case _ => false } )
    )
    if (useFallback)
      return mkFallbackImpl

    val closureTree       = functionToLocalMethod(fnTree)    
    def closure           = closureTree.symbol
    def newBuilder        = c.prefix match {
      case ArrayOpsPrefix(tree) => tree match {
        case Apply(Select(_, _), List(arr)) => arr.tpe.typeSymbol.companionSymbol.typeSignature member 'newBuilder
      }
      case _ => inCollTpe.typeSymbol.companionSymbol.typeSignature member 'newBuilder
    }
    def closureDef        = c.Expr[Unit](closureTree)
    def builderVal0       = ValDef(NoMods, 'b, TypeTree(), bfTree())
    def sizeHintTr        = ('b dot 'sizeHint)(c.prefix.tree)
    
    val builderTpe        = c.typeCheck(Select(bfTree, 'apply)).tpe
    val builderMethodSym  = newLocalMethod(freshName("builder"), Nil, builderTpe)
    val builderDefTr0     = DefDef(NoMods, freshName("builder"), Nil, Nil, TypeTree(builderTpe), Block(List(builderVal0, sizeHintTr), 'b))
    builderDefTr0 setSymbol builderMethodSym
    c.resetAllAttrs(builderDefTr0)
    val builderDefTr      = c.typeCheck(builderDefTr0).asInstanceOf[DefDef]
    def builderDef        =  c.Expr[Unit](builderDefTr)
    def builderDefSym     = builderDefTr.symbol
    def builderVal        =  c.Expr[Unit](ValDef(NoMods, 'buf, TypeTree(), builderDefSym()))
        
    def mkCall(arg: Tree) = c.Expr[Unit](if (isForeach) closure(arg) else ('buf dot '+=)(closure(arg)))
    def mkResult          = c.Expr[Nothing](if (isForeach) mkUnit else 'buf dot 'result)

    def mkMutIndexed[Prefix](prefixTree: Tree): c.Tree = {
      val prefix   = c.Expr[Prefix](prefixTree)
      val len      = c.Expr[Int]('xs dot 'length) // might be array or indexedseq
      val call     = c.Expr[Unit](('buf dot 'update)('i, closure('xs('i))))
      def mkResult = c.Expr[Nothing](if (isForeach) mkUnit else 'buf)

      val arrCons =   Apply(Select(New(TypeTree(outCollTpe)), nme.CONSTRUCTOR), List(('xs dot 'length).lhs))
      val builderVal = c.Expr[Prefix](arrCons)
      
      reify {
        closureDef.splice
        val xs = prefix.splice
        var buf = builderVal.splice
        var i  = 0
        while (i < len.splice) {
          call.splice
          i += 1
        }
        mkResult.splice
      }.tree
    }

    def mkLinear(prefixTree: Tree): c.Tree = {
      val prefix  = c.Expr[Lin[A]](prefixTree)
      val call    = mkCall('these dot 'head)

      reify {
        closureDef.splice
        builderDef.splice
        builderVal.splice
        var these = prefix.splice
        while (!these.isEmpty) {
          call.splice
          these = these.tail
        }
        mkResult.splice
      }.tree
    }

    def mkTraversable(prefixTree: Tree): c.Tree = {
      val prefix  = c.Expr[Traversable[A]](prefixTree)
      val call    = mkCall('it dot 'next)

      reify {
        closureDef.splice
        builderDef.splice
        builderVal.splice
        val it = prefix.splice.toIterator
        while (it.hasNext)
          call.splice

        mkResult.splice
      }.tree
    }

    val resExpr = c.prefix match {
      case ArrayPrefix(tree)       => mkMutIndexed[Array[A]](tree)
      case ArrayOpsPrefix(tree)    => mkMutIndexed[Array[A]](tree dot 'repr) // ArrayOps make things much slower.
      case MutIndexedPrefix(tree)  => mkMutIndexed[MutInd[A]](tree)
      case LinearPrefix(tree)      => mkLinear(tree)
      case TraversablePrefix(tree) => mkTraversable(tree)
      case _                       => mkFallbackImpl
    }

    val tree = flatStats.init match {
      case Nil   => resExpr
      case stats => Block(stats, resExpr)
    }
    
    tree
  }

//  def foreachInfix[A: c0.WeakTypeTag, Coll: c0.WeakTypeTag](c0: CtxColl[A, Coll])(f0: c0.Expr[A => Any]): c0.Expr[Unit] =
//    mapInfix[A, Any, Coll, Unit](c0)(f0)
}
