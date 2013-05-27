package ppl.ltc.ir


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
}

case class EVar(name: HName) extends HExpr
case class ELambda(name: HName, body: HExpr) extends HExpr
case class EApply(fx: HExpr, arg: HExpr) extends HExpr
case class EInt(value: Int) extends HExpr
case class EFmap(f: HFunctor) extends HExpr

