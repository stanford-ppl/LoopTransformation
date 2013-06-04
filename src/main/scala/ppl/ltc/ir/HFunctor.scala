package ppl.ltc.ir

import collection.immutable.Seq

/*
trait HFunctor {
  def apply(t: HType): HType
  def apply(x: HExpr): HExpr = EApply(EFmap(this), x)
}
trait HFunctorRepresentable extends HFunctor

object FList extends HFunctor {
  def apply(t: HType): HType = DList(t)
  override def toString: String = DList.toString
}
case class FDiagonal(size: Int) extends HFunctorRepresentable {
  def apply(t: HType): HType = DDiagonal(size)(t)
  override def toString: String = DDiagonal(size).toString
}
*/
