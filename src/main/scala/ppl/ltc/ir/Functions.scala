package ppl.ltc.ir

/*
object Functions {
  val compose: HExpr = {
    val f = HNameS("f")
    val g = HNameS("g")
    val x = HNameS("x")
    ELambda(f, ELambda(g, ELambda(x, EApply(EVar(f), EApply(EVar(g), EVar(x))))))
  }
  val const: HExpr = {
    val x = HNameS("x")
    val c = HNameS("c")
    ELambda(c, ELambda(x, EVar(c)))
  }
  val identity: HExpr = ELambda(HNameS("x"), EVar(HNameS("x")))
}

object ∘ {
  def unapply(t: HExpr): Option[Tuple2[HExpr, HExpr]] = t match {
    case EApply(EApply(Functions.compose, a), b) => Some((a,b))
    case _ => None
  }
}
*/
