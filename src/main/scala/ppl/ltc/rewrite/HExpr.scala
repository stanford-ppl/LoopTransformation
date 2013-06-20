package ppl.ltc.rewrite



sealed trait HExpr {
  override def toString: String = PrettyPrint.pprint(this)
  def freeIdx: Int = {
    import scala.math.max
    this match {
      case EVar(i, t) => i
      case EApp(f, a) => max(f.freeIdx, a.freeIdx)
      case ETApp(f, a) => f.freeIdx
      case ELambda(d, b) => b.freeIdx - 1
      case ETLambda(d, b) => b.freeIdx
      case EPrimitive(p) => 0
    }
  }
  def freeTIdx: Int = {
    import scala.math.max
    this match {
      case EVar(i, t) => t.freeTIdx
      case EApp(f, a) => max(f.freeTIdx, a.freeTIdx)
      case ETApp(f, a) => max(f.freeTIdx, a.freeTIdx)
      case ELambda(d, b) => max(d.freeTIdx, b.freeTIdx)
      case ETLambda(d, b) => max(0, b.freeTIdx - 1)
      case EPrimitive(p) => 0
    }
  }

  def htype: HType = this match {
    case EVar(i, t) => t
    case EApp(f, a) => {
      val tf = f.htype
      val ta = a.htype
      tf match {
        case TArr(l, r) if l == ta => r
        case _ => {
          println(f)
          println(a)
          println(tf)
          println(ta)
          throw new IRValidationException()
        }
      }
    }
    case ETApp(f, a) => {
      val tf = f.htype
      TApp(tf, a).beta
    }
    case ELambda(d, b) => {
      d --> b.htype
    }
    case ETLambda(d, b) => {
      TLambda(d, b.htype)
    }
    case EPrimitive(p) => p.htype
  }

  def tsub(m: (Int, HKind) => HType): HExpr = this match {
    case EVar(i, t) => EVar(i, t.tsub(m))
    case EApp(f, a) => EApp(f.tsub(m), a.tsub(m))
    case ETApp(f, a) => ETApp(f.tsub(m), a.tsub(m))
    case ELambda(d, b) => ELambda(d.tsub(m), b.tsub(m))
    case ETLambda(d, b) => ETLambda(d, b.tsub((i,k) => if(i == 1) TVar(1, k) else m(i-1,k).tshift))
    case EPrimitive(p) => this
  }

  def tshift: HExpr = tsub((i,k) => TVar(i+1,k))

  def sub(m: (Int, HType) => HExpr): HExpr = this match {
    case EVar(i, t) => {
      val rv = m(i,t)
      if(rv.htype != t) throw new IRValidationException()
      rv
    }
    case EApp(f, a) => EApp(f.sub(m), a.sub(m))
    case ETApp(f, a) => ETApp(f.sub(m), a)
    case ELambda(d, b) => ELambda(d, b.sub((i,t) => if(i == 1) EVar(1, d) else m(i,t).shift))
    case ETLambda(d, b) => ETLambda(d, b.sub(m))
    case EPrimitive(p) => this
  }

  def shift: HExpr = sub((i,t) => EVar(i+1, t))

  def tvarKind(idx: Int): HKind = this match {
    case EVar(i, t) => t.tvarKind(idx)
    case EApp(f, a) => Util.agree(f.tvarKind(idx), a.tvarKind(idx))
    case ETApp(f, a) => Util.agree(f.tvarKind(idx), a.tvarKind(idx))
    case ELambda(d, b) => Util.agree(d.tvarKind(idx), b.tvarKind(idx))
    case ETLambda(d, b) => b.tvarKind(idx+1)
    case EPrimitive(p) => null
  }

  def varType(idx: Int): HType = this match {
    case EVar(i, t) => if(i == idx) t else null
    case EApp(f, a) => Util.agree(f.varType(idx), a.varType(idx))
    case ETApp(f, a) => f.varType(idx)
    case ELambda(d, b) => b.varType(idx+1)
    case ETLambda(d, b) => b.varType(idx)
    case EPrimitive(p) => null
  }

  def apply(x: HExpr): HExpr = EApp(this, x)
  def apply(t: HType): HExpr = ETApp(this, t)
  def ∘(y: HExpr): HExpr = {
    val TArr(lx, rx) = this.htype
    val TArr(ly, ry) = y.htype
    if(ry != lx) throw new IRValidationException()
    EPrimitive(PCompose)(ly)(ry)(rx)(this)(y)
  }
  def *(y: HExpr): HExpr = this ∘ y
}

object ∘ {
  def unapply(x: HExpr): Option[Tuple2[HExpr, HExpr]] = x match {
    case EApp(EApp(ETApp(ETApp(ETApp(EPrimitive(PCompose), a), b), c), f), g) => Some((f, g))
    case _ => None
  }
}

case class EVar(idx: Int, t: HType) extends HExpr { if(idx <= 0) throw new IRValidationException() }
case class EApp(fx: HExpr, arg: HExpr) extends HExpr
case class ETApp(fx: HExpr, arg: HType) extends HExpr
case class ELambda(dom: HType, body: HExpr) extends HExpr
case class ETLambda(dom: HKind, body: HExpr) extends HExpr

case class EPrimitive(p: HPrimitive) extends HExpr
