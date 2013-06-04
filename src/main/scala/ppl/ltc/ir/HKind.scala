package ppl.ltc.ir

sealed trait HKind {
  override def toString: String = PrettyPrint.pprint(this)
}

object KType extends HKind
case class KArr(p: Polarity, lhs: HKind, rhs: HKind) extends HKind

