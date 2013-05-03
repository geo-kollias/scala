package scala.tools.reflect.declosurify

object Declosurify {
  def mapInfix[A, B](c0: Ctx)(f0: c0.Expr[A => B], inElemTpe: c0.Type, outElemTpe: c0.Type, inCollTpe: c0.Type, outCollTpe: c0.Type, bfTree: c0.Tree): c0.Tree = {
    val ctx = new MacroSupport[c0.type](c0)
    import ctx._
    import c.universe._
    
    System.err.println("c0 = " + c0)
    System.err.println("c = " + c)
    println(showRaw(c.prefix))
    
    System.err.println("inElemTpe = " + inElemTpe)
    System.err.println("outElemTpe = " + outElemTpe)
    System.err.println("inCollTpe = " + inCollTpe)
    System.err.println("outCollTpe = " + outCollTpe)
    System.err.println("bfTree = " + bfTree)
    System.err.println("bfTree.tpe = " + bfTree.tpe)
 
//    call.log[A, B, Coll, That]("f0" -> f0.tree)	// only for debugging purposes
//    call.log[A, B]("f0" -> f0.tree)   

    def isForeach = outCollTpe =:= typeOf[Unit]
    def mkFallbackImpl: c.Tree = {
      val name: TermName = if (isForeach) "foreachImpl" else "map"
//      val pre = Select(c.prefix.tree, "xs": TermName)
      val pre = c.prefix.tree

      val fallbacktree = Apply(Select(pre, name), f0.tree :: Nil)
      System.err.println("fallbacking... tree = " + fallbacktree)
      fallbacktree	// e.g. scala.this.Predef.println(improving.this.InlinedList.plain2inlinedList[Int](InlinedList.apply[Int](1, 2, 3).xs.map[Int, List[Int]](((x: Int) => x.*(10)))(immutable.this.List.canBuildFrom[Int])))
    }

    println("showRaw(f0.tree) = " + showRaw(f0.tree))
    val flatStats = flatten(f0.tree)
    val fnTree = flatStats.reverse match {
      case (f: Function) :: _ => f
      case _                  => null
    }
    System.err.println("flatStats = " + flatStats)
    System.err.println("fnTree = " + fnTree)
    System.err.println("c.enclosingMethod = " + c.enclosingMethod)
    
    val useFallback = (
         ( fnTree == null)
      || ( c.enclosingMethod == null )
      || ( fnTree exists { case Return(_) => true case _ => false } )
    )
    if (useFallback)
      return mkFallbackImpl

    val closureTree = functionToLocalMethod(fnTree)
    System.err.println("closureTree = " + closureTree)
    
    def closure           = closureTree.symbol
    def newBuilder        = c.prefix match {
      case ArrayOpsPrefix(tree) => tree match {
        case Apply(Select(_, _), List(arr)) => arr.tpe.typeSymbol.companionSymbol.typeSignature member 'newBuilder
      }
      case _ => inCollTpe.typeSymbol.companionSymbol.typeSignature member 'newBuilder
    }    
    def closureDef        = c.Expr[Unit](closureTree)
    println("newBuilder(outElemTpe) = " + newBuilder(outElemTpe))
//    def builderVal        = c.Expr[Unit](if (isForeach) mkUnit else ValDef(NoMods, 'buf, TypeTree(), newBuilder(outElemTpe)))
    
//    Playing with canBuildFrom:
//    println("bfTree = " + bfTree)
//    def builder = { // extracted to keep method size under 35 bytes, so that it can be JIT-inlined
//      val b = bf(repr)
//      b.sizeHint(this)
//      b
//    }
//    def bf                = bfTree.symbol
//    def prefixTreeSymbol  = c.prefix.tree.symbol
//    def bfExpr            = c.Expr[Unit](bfTree)
//    val builder           = reify({val b = bfExpr.splice(repr); b.sizeHint(this); b})
//    def builderVal        = c.Expr[Unit](ValDef(NoMods, 'buf, TypeTree(), bf(prefixTreeSymbol dot 'repr)))
    
    def builderVal        = c.Expr[Unit](ValDef(NoMods, 'buf, TypeTree(), Apply(bfTree, List())))

    //    def builderVal0        = c.Expr[Unit](ValDef(NoMods, 'buf, TypeTree(), bfTree()))
//    def builderVal         =  DefDef(NoMods, freshName("local"), Nil, List(vparams), TypeTree(frestpe), c.resetAllAttrs(fbody.duplicate))
    println("builderVal = " + builderVal)
        
    def mkCall(arg: Tree) = c.Expr[Unit](if (isForeach) closure(arg) else ('buf dot '+=)(closure(arg)))
    def mkResult          = c.Expr[Nothing](if (isForeach) mkUnit else 'buf dot 'result)
    
    System.err.println("c.prefix = " + c.prefix)
    System.err.println("c.prefix.actualType = " + c.prefix.actualType)
    
    def mkMutIndexed[Prefix](prefixTree: Tree): c.Tree = {
      System.err.println("mkMutIndexed: prefixTree = " + prefixTree + ", showRaw(weakTypeOf[Prefix]) = " + showRaw(weakTypeOf[Prefix]))
      val prefix = c.Expr[Prefix](prefixTree)
      val len    = c.Expr[Int]('xs dot 'length) // might be array or indexedseq
      val call   = c.Expr[Unit](('buf dot 'update)('i, closure('xs('i))))
      def mkResult          = c.Expr[Nothing](if (isForeach) mkUnit else 'buf)

      val arrCons =   Apply(Select(New(TypeTree(outCollTpe)), nme.CONSTRUCTOR), List(('xs dot 'length).lhs))
      val builderVal = c.Expr[Prefix](arrCons)
      
      reify {
        closureDef.splice
        val xs = prefix.splice
        var buf = builderVal.splice
        var i  = 0
        while (i < len.splice) {
//          System.err.println("in indexed while...")
          call.splice
          i += 1
        }
        mkResult.splice
      }.tree
    }
    
    def mkImmutIndexed[Prefix](prefixTree: Tree): c.Tree = {
      System.err.println("mkImmutIndexed: prefixTree = " + prefixTree)
      val prefix = c.Expr[Prefix](prefixTree)
      val len    = c.Expr[Int]('xs dot 'length) // might be array or indexedseq
      val call   = mkCall('xs('i))

      reify {
        closureDef.splice
        builderVal.splice
        val xs = prefix.splice
        var i  = 0
        while (i < len.splice) {
          call.splice
          i += 1
        }
        mkResult.splice
      }.tree
    }

    def mkLinear(prefixTree: Tree): c.Tree = {
      System.err.println("mkLinear: prefixTree = " + prefixTree)
      val prefix    = c.Expr[Lin[A]](prefixTree)
      val call = mkCall('these dot 'head)

      reify {
        closureDef.splice
        builderVal.splice
        var these = prefix.splice
        while (!these.isEmpty) {
//          System.err.println("in linear while...")
          call.splice
          these = these.tail
        }
        mkResult.splice
      }.tree
    }

    def mkTraversable(prefixTree: Tree): c.Tree = {
      System.err.println("mkTraversable: prefixTree = " + prefixTree)
      val prefix = c.Expr[Traversable[A]](prefixTree)
      val call   = mkCall('it dot 'next)

      reify {
        closureDef.splice
        builderVal.splice
        val it = prefix.splice.toIterator
        while (it.hasNext) {
//          System.err.println("in traversable while...")
          call.splice
        }

        mkResult.splice
      }.tree
    }

//    System.err.println("c.prefix = " + c.prefix)
    val resExpr = c.prefix match {
      case ArrayPrefix(tree)       => mkMutIndexed[Array[A]](tree)
      case ArrayOpsPrefix(tree)    => mkMutIndexed[Array[A]](tree dot 'repr) // ArrayOps make things much slower.
      case MutIndexedPrefix(tree)  => mkMutIndexed[MutInd[A]](tree)
      case ImmutIndexedPrefix(tree)=> mkImmutIndexed[ImmutInd[A]](tree)
      case LinearPrefix(tree)      => mkLinear(tree)
      case TraversablePrefix(tree) => mkTraversable(tree)
      case _                       => mkFallbackImpl
    }
    System.err.println("resExpr = " + resExpr)
    System.err.println("showRaw(resExpr) = " + showRaw(resExpr))

    val tree = flatStats.init match {
      case Nil   => resExpr
      case stats => Block(stats, resExpr)
    }
    System.err.println("final result tree = " + tree)
    
    tree
  }

//  def foreachInfix[A: c0.WeakTypeTag, Coll: c0.WeakTypeTag](c0: CtxColl[A, Coll])(f0: c0.Expr[A => Any]): c0.Expr[Unit] =
//    mapInfix[A, Any, Coll, Unit](c0)(f0)
}
