package ppl.ltc.ir

object PrettyPrint {
  def pprint(hkind: HKind): String = pprint(hkind, 10)

  def pprint(hkind: HKind, pri: Int): String = {
    val (opri, rv) = hkind match {
      case KType => (0, "★")
      case KArr(l, r) => (1, pprint(l, 0) + " → " + pprint(r, 1))
    }
    if(pri < opri) {
      "(" + rv + ")"
    }
    else {
      rv
    }
  }

  def pprint(htype: HPolyType): String = pprint(htype, 0, 10)

  def pprint(htype: HPolyType, ld: Int, pri: Int): String = {
    val (opri, rv) = htype match {
      case TVar(i) => (0, if(i <= ld) ('α' + (ld - i)).toChar.toString else ("T" + i.toString))
      case TArr(l, r) => (2, pprint(l, ld, 1) + " ——> " + pprint(r, ld, 2))
      case TApp(f, a) => (1, pprint(f, ld, 1) + " " + pprint(a, ld, 0))
      case TLambda(d, b) => (3, "Λ (" + ('α' + ld).toChar.toString + ": " + pprint(d) + "). " + pprint(b, ld+1, 3))
      case TAll(d, b) => (3, "∀ (" + ('α' + ld).toChar.toString + ": " + pprint(d) + "). " + pprint(b, ld+1, 3))
    }
    if(pri < opri) {
      "(" + rv + ")"
    }
    else {
      rv
    }
  }

  
  def pprint(hexpr: HExpr): String = pprint(hexpr, 0, 0, 10)

  def pprint(hexpr: HExpr, ld: Int, tld: Int, pri: Int): String = {
    val (opri, rv) = hexpr match {
      case EVar(i) => (0, if(i <= ld) ('a' + (ld - i)).toChar.toString else ("X" + i.toString))
      case EApp(f, a) => (2, pprint(f, ld, tld, 2) + " " + pprint(a, ld, tld, 1))
      //case ETApp(f, a) => (1, pprint(f, ld, tld, 1) + "[" + pprint(a, tld, 10) + "]")
      case ELambda(b) => (4, "λ (" + ('a' + ld).toChar.toString + ". " + pprint(b, ld+1, tld, 4))
      //case ETLambda(d, b) => (4, "Λ (" + ('α' + tld).toChar.toString + ": " + pprint(d) + "). " + pprint(b, ld, tld+1, 4))
      //case ETAll(d, b) => (4, "∀ (" + ('α' + tld).toChar.toString + ": " + pprint(d) + "). " + pprint(b, ld, tld+1, 4))
    }
    if(pri < opri) {
      "(" + rv + ")"
    }
    else {
      rv
    }
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

