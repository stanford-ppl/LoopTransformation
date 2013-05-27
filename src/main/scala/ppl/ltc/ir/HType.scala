package ppl.ltc.ir

import scala.collection._

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
