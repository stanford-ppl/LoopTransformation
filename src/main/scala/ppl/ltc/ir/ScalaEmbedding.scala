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

  class HExprHack(x: HExpr) {
    def apply(y: HExpr): HExpr = EApply(x, y)
    def *(y: HExpr): HExpr = {
      val n = freshVar
      ELambda(n, EApply(x, EApply(y, EVar(n))))
    }
  }
  implicit def hexpr2hexprhack(x: HExpr) = new HExprHack(x)

  class HFunctorHack(f: HFunctor) {
    def apply(x: HExpr): HExpr = EApply(EFmap(f), x)
  }
  implicit def hfunctor2functorhack(f: HFunctor) = new HFunctorHack(f)
}


object Stuff {
  val sce = new ScalaEmbedding()
  import sce._
  
  val lpre = elambda(f => elambda(g => FList(f) * FList(g)))

}