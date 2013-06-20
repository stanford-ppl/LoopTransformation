package ppl.ltc.rewrite

import ScalaEmbedding._

sealed trait HPrimitive {
  val name: String
  val htype: HType
}

object PCompose extends HPrimitive {
  val name = "(∘)"
  val htype: HType = tlambda(KType, a => tlambda(KType, b => tlambda(KType, c => 
    (b --> c) --> ((a --> b) --> (a --> c)))))
}

/*
case class PCompose(arity: Int) extends HPrimitive {
  if(arity < 2) throw new IRValidationException
  val name = if(arity == 2) "(∘)" else "compose" + arity.toString
  val htype: HType = {
    var rv: HType = TVar(arity+1, KType) --> TVar(1, KType)
    for(i <- 0 until arity) {
      rv = ((TVar(arity+1-i, KType) --> TVar(arity-i, KType)) --> rv)
    }
    for(i <- 0 until arity) {
      rv = TLambda(KType, rv)
    }
    rv
  }
}
*/
