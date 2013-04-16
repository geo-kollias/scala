package scala.tools.reflect.declosurify

object Declosurify {
  def mapInfix[A, B](c0: Ctx)(f0: c0.Expr[A => B], inElemTpe: c0.Type, outElemTpe: c0.Type, inCollTpe: c0.Type, outCollTpe: c0.Type, bfTree: c0.Tree): c0.Tree = {
    val ctx = new MacroSupport[c0.type](c0)
    import ctx._
    import c.universe._
    
    System.err.println("c0 = " + c0)
    System.err.println("c = " + c)
    println(showRaw(c.prefix))
 
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
    
    System.err.println("flatStats = " + flatStats)
    System.err.println("fnTree = " + fnTree)

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
    def builderVal        = c.Expr[Unit](if (isForeach) mkUnit else ValDef(NoMods, 'buf, TypeTree(), newBuilder(outElemTpe)))
    
//    Playing with canBuildFrom:
//    println("bfTree = " + bfTree)
//    def builder = { // extracted to keep method size under 35 bytes, so that it can be JIT-inlined
//      val b = bf(repr)
//      b.sizeHint(this)
//      b
//    }
//    def bf                = bfTree.symbol
//    def bfExpr            = c.Expr[Unit](bfTree)
//    val builder           = reify({val b = bfExpr.splice(repr); b.sizeHint(this); b})
//    val tmpTree = bfTree.symbol(outElemTpe)
//    def builderVal        = c.Expr[Unit](ValDef(NoMods, 'buf, TypeTree(), tmpTree('xs dot 'repr)))
//    println("bf('repr) = " + bf('repr))
    
    def mkCall(arg: Tree) = c.Expr[Unit](if (isForeach) closure(arg) else ('buf dot '+=)(closure(arg)))
    def mkResult          = c.Expr[Nothing](if (isForeach) mkUnit else 'buf dot 'result)
    
    System.err.println("c.prefix = " + c.prefix)
    System.err.println("c.prefix.actualType = " + c.prefix.actualType)
    
    def mkIndexed[Prefix: WeakTypeTag](prefixTree: Tree): c.Tree = {
      System.err.println("mkIndexed: prefixTree = " + prefixTree)
      val prefix = c.Expr[Prefix](prefixTree)
      val len    = c.Expr[Int]('xs dot 'length) // might be array or indexedseq
      val call   = mkCall('xs('i))

      reify {
        closureDef.splice
        builderVal.splice
        val xs = prefix.splice
        var i  = 0
        while (i < len.splice) {
//          System.err.println("in indexed while...")
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

//    def mkTraversable(prefixTree: Tree): c.Expr[That] = {
//      val prefix = c.Expr[Traversable[A]](prefixTree)
//      val call   = mkCall('it dot 'next)
//
//      reify {
//        closureDef.splice
//        builderVal.splice
//        val it = prefix.splice.toIterator
//        while (it.hasNext) {
////          System.err.println("in traversable while...")
//          call.splice
//        }
//
//        mkResult.splice
//      }
//    }

//    System.err.println("c.prefix = " + c.prefix)
    val resExpr = c.prefix match {
      case ArrayPrefix(tree)       => mkIndexed[Array[A]](tree)
      case ArrayOpsPrefix(tree)    => mkIndexed[Array[A]](tree)
//      case IndexedPrefix(tree)     => mkIndexed[Ind[A]](tree)
      case LinearPrefix(tree)      => mkLinear(tree)
//      case TraversablePrefix(tree) => mkTraversable(tree)
      case _                       => mkFallbackImpl
    }
//    System.err.println("resExpr = " + resExpr)

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
