package ppl.ltc.rewrite


sealed trait HKind {
  override def toString: String = PrettyPrint.pprint(this)
  def -->+(c: HKind): HKind = KArr(Positive, this, c)
  def -->-(c: HKind): HKind = KArr(Negative, this, c)
}

object KType extends HKind
case class KArr(p: Polarity, lhs: HKind, rhs: HKind) extends HKind
