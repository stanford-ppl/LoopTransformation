package ppl.ltc.ir

import scala.collection._

sealed trait HType {
  override def toString: String = this match {
    case TInt() => "Int"
    case TParam(i) => ("α"(0) + i).toChar.toString
    case TFunctor(f, t) => f.toString + "[" + t.toString + "]"
    case TArrow(d: TArrow, c) => "(" + d.toString + ") --> " + c.toString
    case TArrow(d, c) => d.toString + " --> " + c.toString
  }
  def -->(c: HType): HType = TArrow(this, c)
  def subst(m: Map[Int, HType]): HType = this match {
    case TInt() => this
    case TParam(i) => m.getOrElse(i, this)
    case TArrow(d, c) => TArrow(d.subst(m), c.subst(m))
    case TFunctor(f, t) => TFunctor(f, t.subst(m))
  }
  def params: Seq[Int] = this match {
    case TInt() => Seq()
    case TParam(i) => Seq(i)
    case TArrow(d, c) => {
      val dp = d.params
      dp ++ c.params.filter(p => !dp.contains(p))
    }
    case TFunctor(f, t) => t.params
  }
  //renames the params in this type to be "canonical"
  def canonicalize: HType = {
    val pp = params
    subst(Map((for(i <- 0 until pp.length) yield (pp(i) -> TParam(i))):_*))
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
