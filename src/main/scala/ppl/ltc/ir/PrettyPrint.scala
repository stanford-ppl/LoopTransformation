package ppl.ltc.ir

object PrettyPrint {
  def pprint(hexpr: HExpr): String = pprint(hexpr, 10)

  def pprint(hexpr: HExpr, pri: Int): String = {
    val (opri, rv) = hexpr match {
      case Functions.const => (0, "K")
      case Functions.identity => (0, "I")
      case a ∘ b => (2, pprint(a, 1) + " ∘ " + pprint(b, 2))
      case Functions.compose => (0, "(∘)")
      case EVar(n) => (0, n.toString)
      case ELambda(n, b) => (4, "λ " + n.toString + ". " + pprint(b, 4))
      case EApply(fx, arg) => (1, pprint(fx, 1) + " " + pprint(arg, 0))
      case x: EPrimitive => (0, x.toString)
    }
    if(pri < opri) {
      "(" + rv + ")"
    }
    else {
      rv
    }
  }
}