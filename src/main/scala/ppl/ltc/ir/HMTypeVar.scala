package ppl.ltc.ir

import scala.collection.immutable.Seq
import scala.collection.immutable.Set


trait HMHasTypeVars[T] {
  self: Product =>
  // get the free variables for this type
  def freeVars: Set[HMTypeVar] = {
    var rv = Set[HMTypeVar]()
    for(x <- productIterator) {
      if(x.isInstanceOf[HMHasTypeVars[_]]) {
        rv = rv union x.asInstanceOf[HMHasTypeVars[_]].freeVars
      }
    }
    rv
  }
  // reconstruct this node using its copy constructor with new inputs
  private def reconstruct(data: Seq[_]): T = {
    val mcp = this.getClass.getDeclaredMethod("copy", (for(x <- productIterator.toSeq) yield x.getClass):_*)
    mcp.invoke(this, (data map (d => d.asInstanceOf[java.lang.Object])):_*).asInstanceOf[T]    
  }
  // alpha substitution
  def alphaSubstitute(sym: HMTypeVar, repl: HMType): T = {
    val ldx = for(x <- productIterator) yield {
      x match {
        case xx: HMHasTypeVars[_] => xx.alphaSubstitute(sym, repl)
        case _ => x
      }
    }
    reconstruct(Seq(ldx.toSeq:_*))
  }
  // produces canonical alpha renaming
  def alphaRename: T = {
    
  }
}



