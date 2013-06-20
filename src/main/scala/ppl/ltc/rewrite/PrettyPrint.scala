package ppl.ltc.rewrite

object PrettyPrint {

  private var displayContext: Boolean = false

  def contextOff { displayContext = false }
  def contextOn { displayContext = true }

  case class PP(val opri: Int, val rv: String) {
    def req(pri: Int): String = {
      if(pri < opri) {
        "(" + rv + ")"
      }
      else {
        rv
      }
    }
  }

  def pprint(x: HKind): String = pps(x).rv
  def pprint(x: HType): String = {
    val fti = x.freeTIdx
    var rv = pps(x, fti).rv
    if(displayContext) {
      var ifx = " ├– "
      for(i <- 1 to fti) yield {
        val k = x.tvarKind(i)
        if(k != null) {
          rv = ('α' + (fti - i)).toChar.toString + ": " + pps(k).rv + ifx + rv
          ifx = ", "
        }
      }
    }
    rv
  }
  def pprint(x: HExpr): String = {
    val fi = x.freeIdx
    val fti = x.freeTIdx
    var rv = pps(x, fi, fti).rv
    if(displayContext) {
      var ifx = " ├– "
      for(i <- 1 to fi) yield {
        val t = x.varType(i)
        if(t != null) {
          rv = ('a' + (fi - i)).toChar.toString + ": " + pps(t, fti).rv + ifx + rv
          ifx = ", "
        }
      }
      ifx = " ├– "
      for(i <- 1 to fti) yield {
        val k = x.tvarKind(i)
        if(k != null) {
          rv = ('α' + (fti - i)).toChar.toString + ": " + pps(k).rv + ifx + rv
          ifx = ", "
        }
      }
    }
    rv
  }

  def pps(x: HKind): PP = x match {
    case KType => PP(0, "★")
    case KArr(p, l, r) => PP(1, pps(l).req(0) + " →" + p.toString + " " + pps(r).req(1))
  }

  def pps(x: HType, tld: Int): PP = x match {
    case TVar(i, k) => PP(0, if(i <= tld) ('α' + (tld - i)).toChar.toString else ("T" + i.toString))
    case TArr(l, r) => PP(2, pps(l, tld).req(1) + " ——> " + pps(r, tld).req(2))
    case TApp(f, a) => PP(1, pps(f, tld).req(1) + " " + pps(a, tld).req(0))
    case TLambda(d, b) => PP(3, "Λ (" + ('α' + tld).toChar.toString + ": " + pps(d).rv + "). " + pps(b, tld+1).req(3))
    case p: TPrimitive => PP(0, p.name)
  }

  def pps(x: HExpr, ld: Int, tld: Int): PP = x match {
    case f ∘ g => {
      PP(3, pps(f, ld, tld).req(2) + " ∘ " + pps(g, ld, tld).req(2))
    }
    case EVar(i, t) => PP(0, if(i <= ld) ('a' + (ld - i)).toChar.toString else ("X" + i.toString))
    case EApp(f, a) => PP(2, pps(f, ld, tld).req(2) + " " + pps(a, ld, tld).req(1))
    case ETApp(f, a) => PP(1, pps(f, ld, tld).req(1) + "[" + pps(a, tld).rv + "]")
    case ELambda(d, b) => PP(6, "λ (" + ('a' + ld).toChar.toString + ": " + pps(d, tld).rv + "). " + pps(b, ld+1, tld).req(6))
    case ETLambda(d, b) => PP(6, "Λ (" + ('α' + tld).toChar.toString + ": " + pps(d).rv + "). " + pps(b, ld, tld+1).req(6))
    case p: EPrimitive => PP(0, p.name)
  }
}

