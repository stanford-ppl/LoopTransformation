package ppl.ltc.ir

import scala.collection.immutable.Seq
import scala.collection.immutable.Map

sealed trait HMExpr extends HMHasExprVars[HMExpr] {
  /* the type of this expression */ 
  val hmtype: HMType
}

/* function application */
case class HMEApply(val fx: HMExpr, val arg: HMExpr) extends HMExpr {
  val hmtype: HMType = (fx.hmtype, arg.hmtype) match {
    case ((td --> tc), tx) if (tx == td) => tc
    case _ => throw new IRValidationException()
  }
  override def toString: String = fx.toString + "(" + arg.toString + ")"
  override def lambdaToPointfree(r: HMExprVar): HMExpr = {

  } 
}

/* lambda */
case class HMELambda(val l: HMExprVar, val body: HMExpr) extends HMExpr {
  val hmtype: HMType = l.hmtype --> body.hmtype
  override def freeVars: Seq[HMExprVar] = {
    val bfv = body.freeVars
    if(bfv exists (v => ((v.index == l.index)&&(v.hmtype != l.hmtype)))) throw new IRValidationException()
    bfv filter (v => (v != l))
  }
  override def alphaSubstitute(repls: Map[HMExprVar, HMExpr]): HMExpr = {
    for(v <- body.freeVars) {
      if((v != l)&&(repls.contains(v))&&(repls(v).freeVars contains l)) throw new IRValidationException()
    }
    HMELambda(l, body.alphaSubstitute(repls - l))
  }
  override def alphaRenameWith(bvs: Seq[HMExprVar]): HMExpr = {
    HMELambda(HMExprVar(l.hmtype, bvs.length), body.alphaRenameWith(bvs :+ l))
  }
  override def toString: String = "λ " + l.toString + ". " + body.toString
  override def toPointfree: HMExpr = {
    if(body.freeVars contains l) {
      body.toPointfree.lambdaToPointfree(l)
    }
    else {
      HMEApply(HMEConst(body.hmtype, l.hmtype), body)
    }
  }
}

/* variable */
case class HMExprVar(val hmtype: HMType, val index: Int) extends HMExpr {
  override def freeVars: Seq[HMExprVar] = Seq(this)
  override def alphaSubstitute(repls: Map[HMExprVar, HMExpr]): HMExpr = {
    repls.getOrElse(this, this)
  }
  override def alphaRenameWith(bvs: Seq[HMExprVar]): HMExpr = {
    for(i <- 0 until bvs.length) {
      if (bvs(i) == this) return HMExprVar(hmtype, i)
    }
    throw new IRValidationException()
  }
  override def toString: String = ("a"(0) + index).toChar.toString
}


/* identity function (I) */
case class HMEIdentity(val t: HMType) extends HMExpr {
  val hmtype: HMType = (t --> t)
  override def toString: String = "id[" + t.toString + "]"
  def lambdaToPointfree(r: HMExprVar): HMExpr = throw new IRValidationException()
}

/* constant function generator (K) */
case class HMEConst(val a: HMType, val b: HMType) extends HMExpr {
  val hmtype: HMType = (a --> (b --> a))
  override def toString: String = "K[" + b.toString + "]"
}

/* substitution function (S) */
case class HMESubstitute(val )

/* a basic composition combinator */
case class HMECompose(val a: HMType, val b: HMType, val c: HMType) extends HMExpr {
  val hmtype: HMType = (a --> b) --> ((b --> c) --> (a --> c))
  //override def toString: String = "(" + fx1.toString + " ∘ " + fx2.toString + ")"
  override def toString: String = "(∘)"
}

/* basic fmap function */
case class HMEFmap(val functor: HMFunctor, val a: HMType, val b: HMType) extends HMExpr {
  val hmtype: HMType = (a --> b) --> (functor(a) --> functor(b))
  override def toString: String = "fmap[" + functor.toString + "]"
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

