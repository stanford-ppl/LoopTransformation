package ppl.ltc.ir


sealed trait HExpr {
  override def toString: String = this match {
    case EVar(n) => n.toString
    case ELambda(n, b) => "(λ " + n.toString + ". " + b.toString + ")"
    case EApply(fx, arg) => "(" + fx.toString + " " + arg.toString + ")"
    case EInt(v) => v.toString
    case EFmap(f) => "fmap{" + f.toString + "}"
  }
}

case class EVar(name: HName) extends HExpr
case class ELambda(name: HName, body: HExpr) extends HExpr
case class EApply(fx: HExpr, arg: HExpr) extends HExpr
case class EInt(value: Int) extends HExpr
case class EFmap(f: HFunctor) extends HExpr

