package ppl.ltc.ir

import scala.collection.immutable.Seq

sealed trait HMExpr {
  /* the number of qualified type variables appearing in this expression */ 
  val hmtype: HMType
  /* specialize this expression with a type specialization */
  def specialize(op: HMSpecialization): HMExpr
}

/* a basic application combinator */
case class HMEApply(val fx: HMExpr, val arg: HMExpr) extends HMExpr {
  if(fx.hmtype.tarity != arg.hmtype.tarity) throw new IRValidationException()
  val hmtype: HMType = {
    fx.hmtype match {
      case HMTApply(tarity, HMTPFunction, Seq(tdomain, tcodomain)) => {
        if(tdomain != arg.hmtype) throw new IRValidationException()
        tcodomain
      }
      case _ => throw new IRValidationException()
    }
  }
  def specialize(op: HMSpecialization): HMExpr = HMEApply(fx.specialize(op), arg.specialize(op))
}

/* function composition */
case class HMECompose(val a: HMType, val b: HMType, val c: HMType) extends HMExpr {
  if(a.tarity != b.tarity) throw new IRValidationException()
  if(b.tarity != c.tarity) throw new IRValidationException()
  val hmtype: HMType = (a --> b) --> ((b --> c) --> (a --> c))
  def specialize(op: HMSpecialization): HMExpr = {
    HMECompose(a.specialize(op), b.specialize(op), c.specialize(op))
  }
}
