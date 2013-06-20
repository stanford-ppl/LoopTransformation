package ppl.ltc.rewrite


sealed trait HKind {
  override def toString: String = PrettyPrint.pprint(this)
  def -->(c: HKind): HKind = KArr(this, c)
}

object KType extends HKind
case class KArr(lhs: HKind, rhs: HKind) extends HKind
