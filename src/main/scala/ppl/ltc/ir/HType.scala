package ppl.ltc.ir

import scala.collection._


sealed trait HType {
  override def toString: String = PrettyPrint.pprint(this)
  def freeIdx: Int = {
    import scala.math.max
    this match {
      case TVar(i) => i
      case TArr(l, r) => max(l.freeIdx, r.freeIdx)
      case TApp(f, a) => max(f.freeIdx, a.freeIdx)
      case TLambda(d, b) => max(0, b.freeIdx - 1)
      case PVar(i) => i
      case PApp(f, a) => max(f.freeIdx, a.freeIdx)
      case PLambda(d, b) => max(0, b.freeIdx - 1)
      case PAllM(d, b) => max(0, b.freeIdx - 1)
      case PAllP(d, b) => max(0, b.freeIdx - 1)
    }
  }
  def freeKindIdx: Int = {
    import scala.math.max
    this match {
      case TVar(i) => 0
      case TArr(l, r) => max(l.freeKindIdx, r.freeKindIdx)
      case TApp(f, a) => max(f.freeKindIdx, a.freeKindIdx)
      case TLambda(d, b) => max(d.freeIdx, b.freeKindIdx)
      case PVar(i) => 0
      case PApp(f, a) => max(f.freeKindIdx, a.freeKindIdx)
      case PLambda(d, b) => max(d.freeIdx, b.freeKindIdx)
      case PAllM(d, b) => max(d.freeIdx, b.freeKindIdx)
      case PAllP(d, b) => max(d.freeIdx, b.freeKindIdx)
    }
  }
}

sealed trait HMonoType extends HType {
  def -->(c: HMonoType): HMonoType = TArr(this, c)
}

sealed trait HPolyType extends HType

object --> {
  def unapply(t: HMonoType): Option[Tuple2[HMonoType, HMonoType]] = t match {
    case TArr(lhs, rhs) => Some((lhs, rhs))
    case _ => None
  }
}

case class TVar(idx: Int) extends HMonoType { if(idx <= 0) throw new IRValidationException() }
case class TArr(lhs: HMonoType, rhs: HMonoType) extends HMonoType
case class TApp(fx: HMonoType, arg: HMonoType) extends HMonoType
case class TLambda(dom: HKind, body: HMonoType) extends HMonoType

case class PVar(idx: Int) extends HPolyType { if(idx <= 0) throw new IRValidationException() }
case class PApp(fx: HPolyType, arg: HMonoType) extends HPolyType
case class PLambda(dom: HKind, body: HPolyType) extends HPolyType
case class PAllM(dom: HKind, body: HMonoType) extends HPolyType
case class PAllP(dom: HKind, body: HPolyType) extends HPolyType
object PAll {
  def apply(d: HKind, t: HType): HPolyType = t match {
    case tm: HMonoType => PAllM(d, tm)
    case tp: HPolyType => PAllP(d, tp)
  }
}

/*
sealed trait HType {
  override def toString: String = this match {
    case TParam(i) => ('α' + i).toChar.toString
    case ((d @ (a --> b)) --> c) => "(" + d.toString + ") ——> " + c.toString
    case (d --> c) => d.toString + " ——> " + c.toString
    case TApp(f, Seq()) => f.toString
    case TApp(f, s) => f.toString + s.mkString("[", ",", "]")
  }
  def -->(c: HType): HType = DArrow(this, c)
  def subst(m: Map[Int, HType]): HType = this match {
    case TParam(i) => m.getOrElse(i, this)
    case TApp(f, a) => TApp(f, a map (_.subst(m)))
  }
  def params: Seq[Int] = this match {
    case TParam(i) => Seq(i)
    case TApp(f, a) => a.foldLeft(Seq[Int]())((a, u) => a ++ u.params.filter(p => !a.contains(p)))
  }
  //renames the params in this type to be "canonical"
  def canonicalize: HType = {
    val pp = params
    subst(Map((for(i <- 0 until pp.length) yield (pp(i) -> TParam(i))):_*))
  }
}
object --> {
  def unapply(t: HType): Option[Tuple2[HType, HType]] = t match {
    case TApp(DArrow, Seq(d, c)) => Some((d, c))
    case _ => None
  }
}

case class TParam(id: Int) extends HType
case class TApp(d: HTypeFunction, args: immutable.Seq[HType]) extends HType {
  if(d.arity != args.length) throw new IRValidationException()
}

sealed trait HTypeFunction { 
  val arity: Int
  def apply(args: HType*): HType = {
    if(args.length != arity) throw new IRValidationException()
    TApp(this, immutable.Seq(args:_*))
  }
  override def toString: String = this.getClass.getName.split("\\$").last.split("\\.").last.drop(1)
}

object DArrow extends HTypeFunction { val arity = 2 }

object DProduct extends HTypeFunction { val arity = 2 }

object DList extends HTypeFunction { val arity = 1 }
case class DDiagonal(size: Int) extends HTypeFunction { 
  val arity = 1
  override def toString: String = "∇_" + size.toString
}

object DInt extends HTypeFunction { val arity = 0 }
object DBool extends HTypeFunction { val arity = 0 }
object DDouble extends HTypeFunction { val arity = 0 }
*/
