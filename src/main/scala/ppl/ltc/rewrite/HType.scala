package ppl.ltc.rewrite


sealed trait HType {
  override def toString: String = PrettyPrint.pprint(this)
  def freeTIdx: Int = {
    import scala.math.max
    this match {
      case TVar(i,k) => i
      case TArr(l, r) => max(l.freeTIdx, r.freeTIdx)
      case TApp(f, a) => max(f.freeTIdx, a.freeTIdx)
      case TLambda(d, b) => max(0, b.freeTIdx - 1)
    }
  }

  def hkind: HKind = this match {
    case TVar(i,k) => k
    case TApp(f, a) => {
      val kf = f.hkind
      val ka = a.hkind
      kf match {
        case KArr(l, r) if l == ka => r
        case _ => throw new IRValidationException()
      }
    }
    case TArr(d, b) => {
      val kd = d.hkind
      val kb = b.hkind
      if((kd != KType)||(kb != KType)) throw new IRValidationException()
      KType
    }
    case TLambda(d, b) => {
      d --> b.hkind
    }
  }

  def beta: HType = this match {
    case TApp(TLambda(d, b), t) => {
      b.tsub((i,k) => if(i == 1) t else TVar(i-1, k)).beta
    }
    case _ => this
  }

  def tsub(m: (Int, HKind) => HType): HType = this match {
    case TVar(i, k) => m(i,k)
    case TArr(l, r) => TArr(l.tsub(m), r.tsub(m))
    case TApp(f, a) => TApp(f.tsub(m), a.tsub(m))
    case TLambda(d, b) => TLambda(d, b.tsub((i,k) => if(i == 1) TVar(1,k) else m(i-1,k).tshift))
  }

  def tshift: HType = tsub((i,k) => TVar(i+1,k))

  def tvarKind(idx: Int): HKind = this match {
    case TVar(i, k) => if(idx == i) k else null
    case TArr(l, r) => Util.agree(l.tvarKind(idx), r.tvarKind(idx))
    case TApp(f, a) => Util.agree(f.tvarKind(idx), a.tvarKind(idx))
    case TLambda(d, b) => b.tvarKind(idx+1)
  }

  def -->(c: HType): HType = TArr(this, c)
}

case class TVar(idx: Int, k: HKind) extends HType { if(idx <= 0) throw new IRValidationException() }
case class TArr(lhs: HType, rhs: HType) extends HType
case class TApp(fx: HType, arg: HType) extends HType
case class TLambda(dom: HKind, body: HType) extends HType


