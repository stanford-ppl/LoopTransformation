package ppl.ltc.ir

import scala.collection.immutable.Seq
import scala.collection.immutable.Map

// this class contains the raw mechanics of the type system, including alpha substitution
trait HMHasTypeVars[T] {
  // get the free variables for this type
  def freeVars: Seq[HMTypeVar] = {
    var rv = Seq[HMTypeVar]()
    for(x <- this.asInstanceOf[Product].productIterator) {
      if(x.isInstanceOf[HMHasTypeVars[_]]) {
        rv = rv ++ x.asInstanceOf[HMHasTypeVars[_]].freeVars.filter(a => !rv.contains(a))
      }
    }
    rv
  }
  // reconstruct this node using its copy constructor with new inputs (super sketchy)
  private def reconstruct(data: Seq[_]): T = {
    val mcp = this.getClass.getMethods().filter(m => m.getName() == "copy")
    if(mcp.length != 1) throw new IRValidationException()
    mcp(0).invoke(this, (data map (d => d.asInstanceOf[java.lang.Object])):_*).asInstanceOf[T]    
  }
  // perform alpha substitution
  def alphaSubstitute(src: HMTypeVar, repl: HMType): T = alphaSubstitute(Map(src -> repl))
  // perform multiple alpha substitutions at once
  def alphaSubstitute(repls: Map[HMTypeVar, HMType]): T = {
    val ldx = for(x <- this.asInstanceOf[Product].productIterator) yield {
      x match {
        case xx: HMHasTypeVars[_] => xx.alphaSubstitute(repls)
        case _ => x
      }
    }
    reconstruct(Seq(ldx.toSeq:_*))
  }
  // produces canonical alpha renaming
  def alphaRename: T = {
    val fv = freeVars
    alphaSubstitute(Map((for(i <- 0 until fv.length) yield fv(i) -> HMTypeVar(i)):_*))
  }
  // format this type, with binding variables
  def format: String = {
    var acc: String = ""
    for(v <- freeVars) {
      acc += "∀" + v.toString + ". "
    }
    acc + toString
  }
}

