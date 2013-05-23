package ppl.ltc.ir

import scala.collection.immutable.Seq
import scala.collection.immutable.Map

sealed trait HMExpr extends HMHasExprVars[HMExpr] {
  /* the type of this expression */ 
  val hmtype: HMType
}

/* identity function */
case class HMTIdentity(val t: HMType) extends HMExpr {
  val hmtype: HMType = (t --> t)
  override def toString: String = "id[" + t.toString + "]"
}

/* function application */
// case class HMTApply(val fx: HMExpr, val arg: HMExpr) extends HMExpr {
//   val hmtype: HMType = (fx.hmtype, arg.hmtype) match {
//     case ((td --> tc), tx) if (tx == td) => tc
//     case _ => throw new IRValidationException()
//   }
// }

/* a basic composition combinator */
case class HMECompose(val fx1: HMExpr, val fx2: HMExpr) extends HMExpr {
  val hmtype: HMType = (fx1.hmtype, fx2.hmtype) match {
    case ((td1 --> tc1), (td2 --> tc2)) if (tc1 == td2) => (td1 --> tc2)
    case _ => throw new IRValidationException()
  }
  override def toString: String = "(" + fx1.toString + " ∘ " + fx2.toString + ")"
}

/* basic fmap function */
case class HMEFmap(val functor: HMFunctor, val body: HMExpr) extends HMExpr {
  val hmtype: HMType = body.hmtype match {
    case (td --> tc) => (functor(td) --> functor(tc))
    case _ => throw new IRValidationException()
  }
  override def toString: String = "fmap[" + functor.toString + "](" + body.toString + ")"
}

/* lambda */
case class HMELambda(val l: HMExprVar, val body: HMExpr) extends HMExpr {
  val hmtype: HMType = l.hmtype --> body.hmtype
  override def freeVars: Set[HMExprVar] = {
    val bfv = body.freeVars
    if((bfv + l).size != ((bfv + l) map (v => v.index)).size) throw new IRValidationException()
    bfv - l
  }
  override def alphaSubstitute(repls: Map[HMExprVar, HMExpr]): HMExpr = {
    HMELambda(l, body.alphaSubstitute(repls - l))
  }
  override def toString: String = "λ " + l.toString + ". " + body.toString
}

/* variable */
case class HMExprVar(val hmtype: HMType, val index: Int) extends HMExpr {
  override def freeVars: Set[HMExprVar] = Set(this)
  override def alphaSubstitute(repls: Map[HMExprVar, HMExpr]): HMExpr = {
    repls.getOrElse(this, this)
  }
  override def toString: String = ("a"(0) + index).toChar.toString
}

//it seems like all of the parallel collections we care about are monads,
//in addition to being functors

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

