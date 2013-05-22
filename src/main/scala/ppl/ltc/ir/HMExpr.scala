package ppl.ltc.ir

import scala.collection.immutable.Seq

sealed trait HMExpr extends HMHasTypeVars[HMExpr] {
  /* the type of this expression */ 
  val hmtype: HMType
}

/* a basic composition combinator */
case class HMECompose(val fx1: HMExpr, val fx2: HMExpr) extends HMExpr {
  val hmtype: HMType = (fx1.hmtype, fx2.hmtype) match {
    case ((td1 --> tc1), (td2 --> tc2)) if (tc1 == td2) => (td2 --> tc1)
    case _ => throw new IRValidationException()
  }
}

// /* fmap */
// case class HMEFmap(val functor: HMFunctor, val body: HMExpr) extends HMExpr {
//   if(functor.tarity != body.hmtype.tarity) throw new IRValidationException()
//   val hmtype: HMType = {
//     body.hmtype match {
//       case ((td --> tc)) => {
//         functor(td) --> functor(tc)
//       }
//       case _ => throw new IRValidationException()
//     }
//   }
//   def specialize(op: HMSpecialization): HMExpr = {
//     HMEFmap(functor.specialize(op), body.specialize(op))
//   }
// }

// /* reduce/fold */
// case class HMEReduce(val functor: HMFunctor, val zero: HMExpr, val body: HMExpr) extends HMExpr {
//   if(functor.tarity != zero.hmtype.tarity) throw new IRValidationException()
//   if(functor.tarity != body.hmtype.tarity) throw new IRValidationException()
//   val hmtype: HMType = {
//     body.hmtype match {
//       case (zero.hmtype --> (tz --> zero.hmtype)) => {
//         functor(tz) --> zero.hmtype
//       }
//       case _ => throw new IRValidationException()
//     }
//   }
//   def specialize(op: HMSpecialization): HMExpr = {
//     HMEReduce(functor.specialize(op), zero.specialize(op), body.specialize(op))
//   }
// }

