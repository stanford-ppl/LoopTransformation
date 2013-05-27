package ppl.ltc.ir


class ScalaEmbedding {
  private var freshIdx: Int = 0;
  private def freshVar: HName = {
    val rv = HNameS(("a"(0) + freshIdx).toChar.toString)
    freshIdx += 1
    rv
  }

  def reset() {
    freshIdx = 0
  }

  def elambda(e: EVar => HExpr): HExpr = {
    val n = freshVar
    ELambda(n, e(EVar(n)))
  }
}

