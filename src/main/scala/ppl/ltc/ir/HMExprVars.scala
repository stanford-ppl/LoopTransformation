package ppl.ltc.ir

import scala.collection.immutable.Seq
import scala.collection.immutable.Map

// this class contains the raw mechanics of the type system, including alpha substitution
trait HMHasExprVars[T] extends HMHasTypeVars[T] {
  // get the free variables for this type
  def freeVars: Set[HMExprVar] = {
    var rv = Set[HMExprVar]()
    for(x <- this.asInstanceOf[Product].productIterator) {
      if(x.isInstanceOf[HMHasExprVars[_]]) {
        rv = rv union x.asInstanceOf[HMHasExprVars[_]].freeVars
      }
    }
    // verify that each variable only has one canonical type
    if(rv.size != (rv map (v => v.index)).size) throw new IRValidationException()
    // return rv
    rv
  }
  // perform alpha substitution
  def alphaSubstitute(src: HMExprVar, repl: HMExpr): T = alphaSubstitute(Map(src -> repl))
  // perform multiple alpha substitutions at once
  def alphaSubstitute(repls: Map[HMExprVar, HMExpr]): T = {
    for((src, repl) <- repls) {
      if(src.hmtype != repl.hmtype) throw new IRValidationException()
    }
    if(repls.keySet.size != (repls.keySet map (v => v.index)).size) throw new IRValidationException()
    val ldx = for(x <- this.asInstanceOf[Product].productIterator) yield {
      x match {
        case xx: HMHasExprVars[_] => xx.alphaSubstitute(repls)
        case _ => x
      }
    }
    reconstruct(Seq(ldx.toSeq:_*))
  }
  // produces canonical alpha renaming
  def alphaRename: T = {
    throw new IRValidationException()
  }
}