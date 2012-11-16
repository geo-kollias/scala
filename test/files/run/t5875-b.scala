import scala.reflect.runtime.universe._
import scala.reflect.runtime.{universe => ru}
import scala.reflect.runtime.{currentMirror => cm}
import scala.tools.reflect.ToolBox

object Test {
  def main(args: Array[String]): Unit = {
    def z1(x: Int) = x
    def z2(x: Int*) = x
    def z3(x: => Int) = x
    def z4[T](x: T) = x
    def z5[T](x: T*) = x
    def z6[T](x: => T) = x
    def z7(x: Int)(y: Int) = x
    def z8(x: Int*)(y: Int*) = x
    def z9(x: => Int)(y: => Int) = x
    def z10[T](x: T)(y: T) = x
    def z11[T](x: T*)(y: T*) = x
    def z12[T](x: => T)(y: => T) = x
    
    println(reify(z1 _))
    println(reify(z2 _))
    println(reify(z3 _))    
    println(reify(z4 _))
    println(reify(z5 _))
    println(reify(z6 _))
    println(reify(z7 _))
    println(reify(z8 _))
    println(reify(z9 _))
    println(reify(z10 _))
    println(reify(z11 _))
    println(reify(z12 _))
  }
}
