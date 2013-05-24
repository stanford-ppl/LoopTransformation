package ppl.ltc.ir

import scala.collection._

sealed trait HType {
  override def toString: String = this match {
    case TInt() => "Int"
    case TParam(i) => ("α"(0) + i).toChar.toString
    case TArrow(d, c) => "(" + d.toString + " --> " + c.toString + ")"
    case TFunctor(f, t) => f.toString + "[" + t.toString + "]"
  }
  def -->(c: HType): HType = TArrow(this, c)
  def subst(m: Map[Int, HType]): HType = this match {
    case TInt() => this
    case TParam(i) => m.getOrElse(i, this)
    case TArrow(d, c) => TArrow(d.subst(m), c.subst(m))
    case TFunctor(f, t) => TFunctor(f, t.subst(m))
  }
}
object --> {
  def unapply(t: HType): Option[Tuple2[HType, HType]] = t match {
    case TArrow(d, c) => Some((d, c))
    case _ => None
  }
}

case class TInt() extends HType
case class TArrow(domain: HType, codomain: HType) extends HType
case class TParam(id: Int) extends HType
case class TFunctor(f: HFunctor, t: HType) extends HType
