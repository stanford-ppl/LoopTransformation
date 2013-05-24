package ppl.ltc.ir


trait HFunctor

case class FList() extends HFunctor {
  override def toString: String = "list"
}
case class FDiagonal(size: Int) extends HFunctor {
  override def toString: String = "∇_" + size.toString
}

