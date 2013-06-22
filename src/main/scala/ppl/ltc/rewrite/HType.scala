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
      case p: TPrimitive => 0
    }
  }

  def hkind: HKind = this match {
    case TVar(i,k) => k
    case TApp(f, a) => {
      val kf = f.hkind
      val ka = a.hkind
      kf match {
        case KArr(p, l, r) if l == ka => r
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
      KArr(b.polarityIn(1), d, b.hkind)
    }
    case p: TPrimitive => p.hkind
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
    case p: TPrimitive => p
  }

  def tshift: HType = tsub((i,k) => TVar(i+1,k))

  def tvarKind(idx: Int): HKind = this match {
    case TVar(i, k) => if(idx == i) k else null
    case TArr(l, r) => Util.agree(l.tvarKind(idx), r.tvarKind(idx))
    case TApp(f, a) => Util.agree(f.tvarKind(idx), a.tvarKind(idx))
    case TLambda(d, b) => b.tvarKind(idx+1)
    case p: TPrimitive => null
  }

  def polarityIn(idx: Int): Polarity = this match {
    case TVar(i, k) => if(idx == i) Positive else Constant
    case TArr(l, r) => (-l.polarityIn(idx)) lub (r.polarityIn(idx))
    case TApp(f, a) => {
      f.hkind match {
        case KArr(p, l, r) => p * a.polarityIn(idx)
        case _ => throw new IRValidationException()
      }
    }
    case TLambda(d, b) => b.polarityIn(idx + 1)
    case p: TPrimitive => Constant
  }

  def -->(c: HType): HType = TArr(this, c)
  def apply(t: HType): HType = TApp(this, t)
}

object --> {
  def unapply(t: HType): Option[Tuple2[HType, HType]] = t match {
    case TArr(lhs, rhs) => Some((lhs, rhs))
    case _ => None
  }
}


case class TVar(idx: Int, k: HKind) extends HType { if(idx <= 0) throw new IRValidationException() }
case class TArr(lhs: HType, rhs: HType) extends HType
case class TApp(fx: HType, arg: HType) extends HType
case class TLambda(dom: HKind, body: HType) extends HType

sealed trait TPrimitive extends HType {
  val name: String
  override val hkind: HKind = null
}

object TPList extends TPrimitive {
  val name: String = "list"
  override val hkind: HKind = KType -->+ KType
}

object TPInt extends TPrimitive {
  val name: String = "int"
  override val hkind: HKind = KType
}

object TPFloat extends TPrimitive {
  val name: String = "float"
  override val hkind: HKind = KType
}

object TPBool extends TPrimitive {
  val name: String = "bool"
  override val hkind: HKind = KType
}
