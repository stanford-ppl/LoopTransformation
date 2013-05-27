package ppl.ltc.ir

import scala.collection._

sealed trait HExpr {
  override def toString: String = PrettyPrint.pprint(this)
  def htype: HType = {
    val ti = new TypeInference
    val ttp = ti.constraintsOf(this, collection.immutable.Map[HName, HType]())
    val tmap = ti.solve
    ttp.subst(tmap).canonicalize
  }
  def occurs(n: HName): Boolean = this match {
    case EVar(m) => n == m
    case ELambda(m, u) => (n != m) && (u.occurs(n))
    case EApply(fx, arg) => fx.occurs(n) || arg.occurs(n)
    case _ => false
  }
  def apply(y: HExpr): HExpr = EApply(this, y)
  def compose(y: HExpr): HExpr = {
    EApply(EApply(Functions.compose, this), y)
  }
  def ∘(y: HExpr): HExpr = this.compose(y)
  def *(y: HExpr): HExpr = this.compose(y)
}

case class EVar(name: HName) extends HExpr
case class ELambda(name: HName, body: HExpr) extends HExpr
case class EApply(fx: HExpr, arg: HExpr) extends HExpr

sealed trait EPrimitive extends HExpr {
  override def toString: String = throw new IRValidationException()
  override def htype: HType = throw new IRValidationException()
}

case class EFmap(f: HFunctor) extends EPrimitive {
  override def toString: String = "fmap{" + f.toString + "}"
  override def htype: HType = {
    val a = TParam(0)
    val b = TParam(1)
    (a --> b) --> (f(a) --> f(b))
  }
}
case class EInt(value: Int) extends EPrimitive {
  override def toString: String = value.toString
  override def htype: HType = TApp(DInt, immutable.Seq[HType]())
}
case class EBool(value: Boolean) extends EPrimitive {
  override def toString: String = value.toString
  override def htype: HType = TApp(DBool, immutable.Seq[HType]())
}
case class EDouble(value: Double) extends EPrimitive {
  override def toString: String = value.toString
  override def htype: HType = TApp(DDouble, immutable.Seq[HType]())
}

