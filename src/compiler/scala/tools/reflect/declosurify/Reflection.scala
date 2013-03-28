package scala.tools.reflect.declosurify

trait ImplicitCollectorFunction[M[_], V, R] {
  type MT
  def mt[T: M] : MT
  def create(ts: List[MT], vs: List[V]): R

  def apply[T1: M](vs: V*) : R                             = create(List(mt[T1]), vs.toList)
  def apply[T1: M, T2: M](vs: V*) : R                      = create(List(mt[T1], mt[T2]), vs.toList)
  def apply[T1: M, T2: M, T3: M](vs: V*) : R               = create(List(mt[T1], mt[T2], mt[T3]), vs.toList)
  def apply[T1: M, T2: M, T3: M, T4: M](vs: V*) : R        = create(List(mt[T1], mt[T2], mt[T3], mt[T4]), vs.toList)
  def apply[T1: M, T2: M, T3: M, T4: M, T5: M](vs: V*) : R = create(List(mt[T1], mt[T2], mt[T3], mt[T4], mt[T5]), vs.toList)
}

class Caller(val t: Throwable) {
  def frames = t.getStackTrace.toList dropWhile (_.getClassName.stripSuffix("$") == "scala.tools.reflect.declosurify.Caller")
  def head = frames.head
}
object Caller {
  implicit def caller: Caller = new Caller(new Throwable)
}

trait ReflectionSupport {
  val u: Universe
  import u._

  class TypeArgFunction[R](f: (List[Type], List[(String, Any)]) => R) extends ImplicitCollectorFunction[WeakTypeTag, (String, Any), R] {
    type MT = Type
    def mt[T: WeakTypeTag] : Type = weakTypeOf[T]
    def create(ts: List[MT], vs: List[(String, Any)]) = f(ts, vs)
  }

  class CallerOps(caller: Caller) {
    def create(ts: List[Type], vs: List[(String, Any)]): String = {
      val v_strs = vs.toList map { case (k, v) => k + "=" + v }
      val res = caller.head.callString(ts, v_strs)
      println(res)
      res
    }
    val log = new TypeArgFunction(create)
  }

  def call(implicit caller: Caller) = new CallerOps(caller)

  implicit final class ReflectStackFrame(val frame: StackTraceElement) {
    def isModule   = className endsWith "$"
    def scalaName  = if (isModule) className.init else className
    def clazz      = if (isModule) rootMirror.staticModule(scalaName) else rootMirror.staticClass(scalaName)
    def className  = frame.getClassName
    def methodName = frame.getMethodName
    def line       = frame.getLineNumber
    def file       = frame.getFileName

    def classType  = clazz.typeSignature
    def method     = classType member (methodName: TermName) asMethod
    def methodType = method typeSignatureIn classType
    def tparams    = methodType match {
      case PolyType(tparams, _) => tparams
      case _                    => Nil
    }
    def paramss = method.paramss
    def params  = paramss match {
      case xs :: _ => xs
      case _       => Nil
    }
    def allParams   = paramss.flatten
    def tparamNames = tparams map (_.name)
    def paramNames  = allParams map (_.name)

    def typeArgsString(targs: List[Any]): String = {
      val prepend = if (tparams.size != targs.size) "<error:mismatched params/args>" else ""
      prepend + (
        if (tparams.isEmpty) ""
        else (tparamNames, targs).zipped map (_ + "=" + _) mkString ("[", ", ", "]")
      )
    }

    def mkStringMaxWidth(args: List[Any], width: Int) = {
      val strs = args map ("" + _)
      val cols = strs map (_.length) sum;

      if (cols > width) strs.mkString("\n  ", ",\n  ", "\n")
      else strs mkString ", "
    }

    def callString(targs: List[Type], args: List[Any]): String = {
      method.name + typeArgsString(targs) + "(" + mkStringMaxWidth(args, 80) + ")"
    }

    override def toString = s"""
      |$frame
      |class=$clazz tpe=$classType
      |method=$method tpe=$methodType
      |tparams=$tparams
      |paramss=$paramss
    """
  }
  // Smuggled from the compiler.
  val METHOD = (1L << 6).asInstanceOf[FlagSet]

  def weakTypesOf[T1: WeakTypeTag] : List[Type]                                                    = List(weakTypeOf[T1])
  def weakTypesOf[T1: WeakTypeTag, T2: WeakTypeTag] : List[Type]                                   = List(weakTypeOf[T1], weakTypeOf[T2])
  def weakTypesOf[T1: WeakTypeTag, T2: WeakTypeTag, T3: WeakTypeTag] : List[Type]                  = List(weakTypeOf[T1], weakTypeOf[T2], weakTypeOf[T3])
  def weakTypesOf[T1: WeakTypeTag, T2: WeakTypeTag, T3: WeakTypeTag, T4: WeakTypeTag] : List[Type] = List(weakTypeOf[T1], weakTypeOf[T2], weakTypeOf[T3], weakTypeOf[T4])

  def typesOf[T1: TypeTag, T2: TypeTag] : List[Type]                           = List(typeOf[T1], typeOf[T2])
  def typesOf[T1: TypeTag, T2: TypeTag, T3: TypeTag] : List[Type]              = List(typeOf[T1], typeOf[T2], typeOf[T3])
  def typesOf[T1: TypeTag, T2: TypeTag, T3: TypeTag, T4: TypeTag] : List[Type] = List(typeOf[T1], typeOf[T2], typeOf[T3], typeOf[T4])

  def symbolOf[T: TypeTag] = typeOf[T].typeSymbol
  def mkUnit = Literal(Constant(()))
  def mkApply(x: scala.Symbol)(args: Tree*): Apply = Apply(x, args.toList)
  def flatten(t: Tree): List[Tree] = t match {
    case Block(xs, expr) => xs :+ expr
    case _               => t :: Nil
  }
  def methPart(tree: Tree): Tree = tree match {
    case Apply(fn, _)           => methPart(fn)
    case TypeApply(fn, _)       => methPart(fn)
    case AppliedTypeTree(fn, _) => methPart(fn)
    case _                      => tree
  }

  implicit final class TypeOps(val tp: Type) {
    def typeArgs = tp match {
      case TypeRef(_, _, args) => args
      case _                   => Nil
    }
    def finalResultType: Type = tp match {
      case NullaryMethodType(restpe) => restpe.finalResultType
      case MethodType(_, restpe)     => restpe.finalResultType
      case PolyType(_, restpe)       => restpe.finalResultType
      case tp                        => tp
    }

    def definitionAnnotations = tp.typeSymbol.annotations
    def useAnnotations = tp match {
      case AnnotatedType(annotations, _, _) => annotations
      case _                                => Nil
    }

    def isDefinedWithAnnotation[T <: ScalaAnnotation : TypeTag] = definitionAnnotations exists (_.tpe =:= typeOf[T])
    def isUsedWithAnnotation[T <: ScalaAnnotation : TypeTag]    = useAnnotations exists (_.tpe =:= typeOf[T])

    def isLinearSeqType   = tp <:< typeOf[Lin[_]]
    def isIndexedSeqType  = tp <:< typeOf[Ind[_]]
    def isTraversableType = tp <:< typeOf[Traversable[_]]
    def isArrayType       = tp <:< typeOf[Array[_]]

    def orElse(alt: => Type): Type = if (tp eq NoType) alt else tp
  }

  implicit final class SymbolOps(val sym: Symbol) {
    def ownerChain_s = ownerChain takeWhile (sym => !sym.isPackageClass) mkString " -> "
    def ownerChain: List[Symbol] = sym match {
      case NoSymbol => Nil
      case _        => sym :: sym.owner.ownerChain
    }
    def firstParam = sym.asMethod.paramss.flatten match {
      case Nil    => NoSymbol
      case p :: _ => p
    }
    def producedType: Type = sym match {
      case m: MethodSymbol => m.typeSignature.finalResultType
      case _               => NoType
    }
  }

  implicit def optionTypeIsNoType(tp: Option[Type]): Type    = tp getOrElse NoType
  implicit def optionSymIsNoSym(sym: Option[Symbol]): Symbol = sym getOrElse NoSymbol
  implicit def symbolToTermName(x: scala.Symbol): TermName   = newTermName(encodeName(x.name))
  implicit def symbolToIdent(x: scala.Symbol): Ident         = Ident(x: TermName)
}
