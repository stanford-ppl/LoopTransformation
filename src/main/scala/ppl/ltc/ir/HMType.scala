package ppl.ltc.ir

import scala.collection.immutable.Seq

sealed trait HMType {
  /* the number of qualified type variables appearing in this expression */ 
  val tarity: Int
  def format: String
  override def toString: String = {
    var acc: String = ""
    for(i <- 0 until tarity) {
      acc += "∀" + (0x03B1 + i).toChar.toString + ". "
    }
    acc + format
  }
}

/* type application */
case class HMTApply(val tarity: Int, val primitive: HMTypePrimitive, val args: Seq[HMType]) extends HMType {
  if(args.length != primitive.parity) throw new IRValidationException()
  for(a <- args) {
    if(a.tarity != tarity) throw new IRValidationException()
  }
  def format: String = {
    primitive.format(args map (h => h.format))
  }
}

/* the vidx-th qualified type variable */
case class HMTVariable(val tarity: Int, val vidx: Int) extends HMType {
  if((vidx < 0)||(vidx >= tarity)) throw new IRValidationException()
  def format: String = {
    (0x03B1 + vidx).toChar.toString
  }
}


