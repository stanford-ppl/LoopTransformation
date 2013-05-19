package ppl.ltc.ir

import scala.collection.immutable.Seq

sealed trait HMExpr {
  /* the number of qualified type variables appearing in this expression */ 
  val hmtype: HMType
  /* specialize this expression with a type specialization */
  def specialize(op: HMSpecialization): HMExpr
}

/* a basic composition combinator */
case class HMECompose(val fx1: HMExpr, val fx2: HMExpr) extends HMExpr {
  if(fx1.hmtype.tarity != fx2.hmtype.tarity) throw new IRValidationException()
  val hmtype: HMType = {
    (fx1.hmtype, fx2.hmtype) match {
      case ((td1 --> tc1), (td2 --> tc2)) => {
        if(td1 != tc2) throw new IRValidationException()
        td2 --> tc1
      }
      case _ => throw new IRValidationException()
    }
  }
  def specialize(op: HMSpecialization): HMExpr = HMECompose(fx1.specialize(op), fx2.specialize(op))
}



