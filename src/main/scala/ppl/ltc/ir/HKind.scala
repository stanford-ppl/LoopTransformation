package ppl.ltc.ir

sealed trait HKind

object KType extends HKind
case class KArr(p: Polarity, lhs: HKind, rhs: HKind) extends HKind

