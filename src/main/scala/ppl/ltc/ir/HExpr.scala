package ppl.ltc.ir


sealed trait HExpr {
  override def toString: String = this match {
    case x if x == Functions.const => "K"
    case x if x == Functions.identity => "I"
    case EApply(EApply(x, a), b) if x == Functions.compose => "(" + a.toString + " ∘ " + b.toString + ")"
    case x if x == Functions.compose => "(∘)"
    case EVar(n) => n.toString
    case EInt(v) => v.toString
    case EFmap(f) => "fmap{" + f.toString + "}"
    case ELambda(n, b) => "λ " + n.toString + ". " + b.toString
    case EApply(fx: ELambda, arg @ (ELambda(_,_) | EApply(_,_))) => "(" + fx.toString + ") (" + arg.toString + ")"
    case EApply(fx: ELambda, arg) => "(" + fx.toString + ") " + arg.toString
    case EApply(fx, arg @ (ELambda(_,_) | EApply(_,_))) => fx.toString + " (" + arg.toString + ")"
    case EApply(fx, arg) => fx.toString + " " + arg.toString
  }
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
  def ∘(y: HExpr): HExpr = {
    EApply(EApply(Functions.compose, this), y)
  }
}

case class EVar(name: HName) extends HExpr
case class ELambda(name: HName, body: HExpr) extends HExpr
case class EApply(fx: HExpr, arg: HExpr) extends HExpr
case class EInt(value: Int) extends HExpr
case class EFmap(f: HFunctor) extends HExpr

