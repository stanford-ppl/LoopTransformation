package ppl.ltc.ir

import scala.collection.immutable.Seq

sealed trait HMTypePrimitive {
  val parity: Int
  def format(args: Seq[String]): String = {
    if(args.length != parity) throw new IRValidationException()
    if(parity == 0) {
      this.toString
    }
    else {
      this.toString + args.mkString("[", ",", "]")
    }
  }
}

object HMTPFunction extends HMTypePrimitive {
  val parity: Int = 2
  override def format(args: Seq[String]): String = {
    if(args.length != parity) throw new IRValidationException()
    "(" + args(0) + " ——> " + args(1) + ")"
  }
}
