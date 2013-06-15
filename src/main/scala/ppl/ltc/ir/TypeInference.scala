package ppl.ltc.ir

import scala.collection._


class TypeInferenceException(msg: String) extends Exception(msg)

object TypeInference {
  var freshIdx: Int = 0
  val constraints = mutable.Stack[(HPolyType, HPolyType)]()


  def fresh: HMonoType = {
    freshIdx += 1
    TVar(freshIdx)
  }

  def occurs(t: HPolyType, id: Int): Boolean = t match {
    case TVar(i) => (i == id)
    case TArr(l, r) => occurs(l, id) || occurs(r, id)
    case TApp(f, a) => occurs(f, id) || occurs(a, id)
    case TLambda(d, b) => occurs(b, id + 1)
    case TAll(d, b) => occurs(b, id + 1)
  }

  def monotypify(t: HPolyType): HMonoType = t match {
    case m: HMonoType => m
    case _ => {
      val tf = fresh
      constraints.push((t, tf))
      tf
    }
  }

  def constraintsOf(e: HExpr, ctx: Seq[HMonoType]): HPolyType = e match {
    case EVar(i) => if(i <= ctx.length) ctx(i-1) else throw new TypeInferenceException("unbound variable: " + i)
    case ELambda(b) => {
      val tf = fresh
      val trv = monotypify(constraintsOf(b, tf +: ctx))
      tf --> trv
    }
    case EApp(e1, e2) => {
      val t1 = constraintsOf(e1, ctx)
      val t2 = monotypify(constraintsOf(e2, ctx))
      val tf = fresh
      constraints.push((t2 --> tf, t1))
      tf
    }
  }

  object TVarEx {
    def unapply(c:(HPolyType, HPolyType)):Option[(Int, HPolyType)] = c match {
      case (TVar(i), t) => Some (i, t)
      case (t, TVar(i)) => Some (i, t)
      case _ => None
    }
  }

  def solve: Map[Int, HPolyType] = {
    val acc = mutable.Map[Int, HPolyType]()
    while(constraints.size > 0) {
      val c = constraints.pop()
      c match {
        case (t1, t2) if t1 == t2 => 
        case TVarEx(i, t) if !occurs(t, i) => {
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


/*
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
    case x: EPrimitive => {
      val xt = x.htype
      val xtpp = xt.params
      xt.subst(Map((for(p <- xtpp) yield (p -> fresh)):_*))
    }
  }

  object TParamEx {
    def unapply(c:(HType, HType)):Option[(Int, HType)] = c match {
      case (TParam(i), t) => Some (i, t)
      case (t, TParam(i)) => Some (i, t)
      case _ => None
    }
  }

  def solve: Map[Int, HType] = {
    val acc = mutable.Map[Int, HType]()
    while(constraints.size > 0) {
      val c = constraints.pop()
      c match {
        case (t1, t2) if t1 == t2 => 
        case TParamEx(i, t) if !occurs(t, i) => {
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
*/

