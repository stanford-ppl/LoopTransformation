package ppl.ltc.ir

import scala.collection.immutable.Seq
import scala.collection.immutable.Map

// this class contains the raw mechanics of the type system, including alpha substitution
trait HMHasTypeVars[T] extends HasReconstruct[T] {
  // get the free variables for this type
  def freeTypeVars: Seq[HMTypeVar] = {
    var rv = Seq[HMTypeVar]()
    for(x <- this.asInstanceOf[Product].productIterator) {
      if(x.isInstanceOf[HMHasTypeVars[_]]) {
        rv = rv ++ x.asInstanceOf[HMHasTypeVars[_]].freeTypeVars.filter(a => !rv.contains(a))
      }
    }
    rv
  }
  // perform alpha substitution
  def alphaTypeSubstitute(src: HMTypeVar, repl: HMType): T = alphaTypeSubstitute(Map(src -> repl))
  // perform multiple alpha substitutions at once
  def alphaTypeSubstitute(repls: Map[HMTypeVar, HMType]): T = {
    val ldx = for(x <- this.asInstanceOf[Product].productIterator) yield {
      x match {
        case xx: HMHasTypeVars[_] => xx.alphaTypeSubstitute(repls)
        case _ => x
      }
    }
    reconstruct(Seq(ldx.toSeq:_*))
  }
  // produces canonical alpha renaming
  def alphaTypeRename: T = {
    val fv = freeTypeVars
    alphaTypeSubstitute(Map((for(i <- 0 until fv.length) yield fv(i) -> HMTypeVar(i)):_*))
  }
  // format this type, with binding variables
  def format: String = {
    var acc: String = ""
    for(v <- freeTypeVars) {
      acc += "∀" + v.toString + ". "
    }
    acc + toString
  }
}

