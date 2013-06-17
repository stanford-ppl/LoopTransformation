package ppl.ltc.ir

sealed trait HKind {
  override def toString: String = PrettyPrint.pprint(this)
  def freeIdx: Int = {
    import scala.math.max
    this match {
      case KVar(i) => i
      case KArr(l, r) => max(l.freeIdx, r.freeIdx)
      case KType => 0
    }
  }
}

case class KVar(idx: Int) extends HKind { if(idx <= 0) throw new IRValidationException() }
object KType extends HKind
case class KArr(lhs: HKind, rhs: HKind) extends HKind

