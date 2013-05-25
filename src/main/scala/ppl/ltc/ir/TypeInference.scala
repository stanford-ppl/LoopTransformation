package ppl.ltc.ir

import scala.collection._

class TypeInferenceException(msg: String) extends Exception(msg)

object TypeInference {
  def occurs(t: HType, id: Int): Boolean = t match {
    case TParam(i) => (i == id)
    case TApp(f, a) => a.exists(occurs(_, id))
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
    case EInt(v) => TApp(DInt, immutable.Seq())
    case EFmap(f) => {
      val ta = fresh
      val tb = fresh
      (ta --> tb) --> (f(ta) --> f(tb))
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
        case (TApp(f1, a1), TApp(f2, a2)) if f1 == f2 => {
          constraints.pushAll(a1.zip(a2))
        }
        case _ => throw new TypeInferenceException("could not unify constraint: " + c.toString)
      }
    }
    acc
  }
}
