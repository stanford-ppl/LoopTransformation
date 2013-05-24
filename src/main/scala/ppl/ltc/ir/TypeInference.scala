package ppl.ltc.ir

import scala.collection._

class TypeInferenceException(msg: String) extends Exception(msg)

object TypeInference {
  def occurs(t: HType, id: Int): Boolean = t match {
    case TParam(i) if i == id => true
    case TArrow(d, c) => occurs(d, id) || occurs(c, id)
    case TFunctor(f, u) => occurs(u, id)
    case _ => false
  }
}

// the is an implementation of Algorithm W using mutable state
class TypeInference {
  import TypeInference._
  var freshIdx: Int = 0
  val constraints = mutable.Stack[(HType, HType)]()

  def fresh: HType = {
    val rv = TParam(freshIdx)
    freshIdx += 1
    rv
  }

  def constraintsOf(e: HExpr, ctx: immutable.Map[HName, HType]): HType = e match {
    // did not implement let polymorphism???
    case EVar(n) => ctx.getOrElse(n, throw new TypeInferenceException("unbound variable: " + n))
    case ELambda(n, b) => {
      val tf = fresh
      val nctx = ctx + (n -> tf)
      val trv = constraintsOf(b, nctx)
      tf --> trv
    }
    case EApply(e1, e2) => {
      val t1 = constraintsOf(e1, ctx)
      val t2 = constraintsOf(e2, ctx)
      val tf = fresh
      constraints.push((t2 --> tf, t1))
      tf
    }
    case EInt(v) => TInt()
    case EFmap(f) => {
      val ta = fresh
      val tb = fresh
      (ta --> tb) --> (TFunctor(f, ta) --> TFunctor(f, tb))
    }
  }

  def solve: Map[Int, HType] = {
    val acc = mutable.Map[Int, HType]()
    while(constraints.size > 0) {
      val c = constraints.pop()
      c match {
        case (t1, t2) if t1 == t2 => 
        //TODO: need to figure out how to do the order-invariant-tuples correctly in scala
        case (TParam(i), t) if !occurs(t, i) => {
          val m = Map(i -> t)
          constraints.transform{case (ta, tb) => (ta.subst(m), tb.subst(m))}
          acc.transform{case (k, t) => t.subst(m)}
          acc += (i -> t)
        }
        case (t, TParam(i)) if !occurs(t, i) => {
          val m = Map(i -> t)
          constraints.transform{case (ta, tb) => (ta.subst(m), tb.subst(m))}
          acc.transform{case (k, t) => t.subst(m)}
          acc += (i -> t)
        }
        case ((ta1 --> ta2), (tb1 --> tb2)) => {
          constraints.push((ta1, tb1))
          constraints.push((ta2, tb2))
        }
        case (TFunctor(f1, t1), TFunctor(f2, t2)) if f1 == f2 => {
          constraints.push((t1, t2))
        }
        case _ => throw new TypeInferenceException("could not unify constraint: " + c.toString)
      }
    }
    acc
  }
}
