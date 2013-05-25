package ppl.ltc.ir

import collection.immutable.Seq

trait HFunctor {
  def apply(t: HType): HType
}

object FList extends HFunctor {
  def apply(t: HType): HType = TApp(DList, Seq(t))
  override def toString: String = DList.toString
}
case class FDiagonal(size: Int) extends HFunctor {
  def apply(t: HType): HType = TApp(DDiagonal(size), Seq(t))
  override def toString: String = DDiagonal(size).toString
}

