package ppl.ltc.ir

object PrettyPrint {
  def pprint(hkind: HKind): String = pprint(hkind, 10)

  def pprint(hkind: HKind, pri: Int): String = {
    val (opri, rv) = hkind match {
      case KType => (0, "★")
      case KArr(p, l, r) => (1, pprint(l, 0) + " →" + p.toString + " " + pprint(r, 1))
    }
    if(pri < opri) {
      "(" + rv + ")"
    }
    else {
      rv
    }
  }


  def pprint(htype: HType): String = pprint(htype, 0)

  def pprint(htype: HType, ld: Int): String = htype match {
    case TVar(i) => if(i <= ld) ('α' + (ld - i)).toChar.toString else ("T" + i.toString)
    case TArr(l, r) => pprint(l, ld) + " ——> " + pprint(r, ld)
    case TLambda(d, b) => "Λ " + ('α' + ld).toChar.toString + ": " + pprint(d) + ". " + pprint(b, ld+1)
    case TApp(fx, arg) => pprint(fx, ld) + " " + pprint(arg, ld)
  }

  /*
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
  */
}

