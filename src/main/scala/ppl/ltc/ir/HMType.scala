package ppl.ltc.ir

import scala.collection.immutable.Seq


trait HMType extends HMHasTypeVars[HMType] {
  self: Product =>
  /* helper method to construct a function type */
  def -->(r: HMType): HMType = HMTFunction(this, r)
  /* format this type, without binding variables */
  def format: String
  /* give the description of this type */
  override def toString: String = {
    var acc: String = ""
    for(v <- freeVars) {
      acc += "∀" + v.format + ". "
    }
    acc + format
  }
}

case class HMTypeVar(index: Int) extends HMType {
  def format: String = (0x03B1 + index).toChar.toString
  override def freeVars: Set[HMTypeVar] = Set(this)
  override def alphaSubstitute(sym: HMTypeVar, repl: HMType): HMType = {
    if(sym == this) repl else this
  }
}

/* function type unapplicator */
object --> {
  def unapply(t: HMType): Option[Tuple2[HMType, HMType]] = t match {
    case HMTFunction(td, tc) => Some((td, tc))
    case _ => None
  }
}

/* type application */
case class HMTFunction(val domain: HMType, val codomain: HMType) extends HMType {
  def format: String = "(" + domain.format + " ——> " + codomain.format + ")"
}



// /* functor type */
// case class HMFunctor(t: HMType) {
//   val tarity: Int = t.tarity - 1
//   if(tarity < 0) throw new IRValidationException()
//   def apply(u: HMType): HMType = {
//     t.specialize(HMSpecialization.last(u))
//   }
//   def specialize(op: HMSpecialization): HMFunctor = {
//     val opp = op.specialize(HMSpecialization.promote(op.tarity))
//     val ops = HMSpecialization(opp.tarity, opp.subs :+ HMTVariable(opp.tarity, op.tarity))
//     HMFunctor(t.specialize(ops))
//   }
// }
