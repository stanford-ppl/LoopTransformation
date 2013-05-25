package ppl.ltc.ir


class ScalaEmbedding {
  private var freshIdx: Int = 0;
  private def freshVar: HName = {
    val rv = HNameS(("a"(0) + freshIdx).toChar.toString)
    freshIdx += 1
    rv
  }


  def elambda(e: EVar => HExpr): HExpr = {
    val n = freshVar
    ELambda(n, e(EVar(n)))
  }

  class HExprHack(x: HExpr) {
    def apply(y: HExpr): HExpr = EApply(x, y)
  }
  implicit def hexpr2hexprhack(x: HExpr) = new HExprHack(x)
}
