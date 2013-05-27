package ppl.ltc.ir


object ScalaEmbedding {
  implicit def str2hname(s: String): HName = HNameS(s)
  implicit def str2hexpr(s: String): HExpr = EVar(HNameS(s))
}

