package ppl.ltc.ir

import scala.collection.immutable.Seq
import scala.collection.immutable.Map

object HMType {
  // gets a type variable that is not in this sequence
  def getNewVar(vars: Seq[HMTypeVar]): HMTypeVar = {
    HMTypeVar(vars.foldLeft(0)((a, u) => if (u.index < a) a else (u.index + 1)))
  }
}

trait HMType extends HMHasTypeVars[HMType] {
  /* helper method to construct a function type */
  def -->(r: HMType): HMType = HMTFunction(this, r)
}

case class HMTypeVar(index: Int) extends HMType {
  override def toString: String = (0x03B1 + index).toChar.toString
  override def freeVars: Seq[HMTypeVar] = Seq(this)
  override def alphaSubstitute(repls: Map[HMTypeVar, HMType]): HMType = {
    repls.getOrElse(this, this)
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
  override def toString: String = "(" + domain.toString + " ——> " + codomain.toString + ")"
}

