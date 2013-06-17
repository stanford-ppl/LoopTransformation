package ppl.ltc.ir

import scala.collection._


class TypeInferenceException(msg: String) extends Exception(msg)

object TypeInference {
  def typeOf(e: HExpr): HType = {
    val ti = new TypeInference
    val t = ti.constraintsOf(e)
    val m = ti.solve
    val ts = canonicalize(subst(t, m))
    val ki = new KindInference
    ki.constraintsOf(ts)
    val kbs = ki.solve
    var s: HType = ts
    for(i <- 0 until ts.freeIdx) {
      s = PAll(kbs(i), s)
    }
    s
  }

  def occurs(t: HMonoType, id: Int): Boolean = t match {
    case TVar(i) => (i == id) 
    case TArr(l, r) => occurs(l, id) || occurs(r, id)
    case TApp(f, a) => occurs(f, id) || occurs(a, id)
    case TLambda(k, b) => occurs(b, id + 1)
  }

  def promote(t: HMonoType): HMonoType = promote(t, 0)

  def promote(t: HMonoType, ab: Int): HMonoType = t match {
    case TVar(i) => if(i > ab) TVar(i + 1) else TVar(i)
    case TArr(l, r) => TArr(promote(l, ab), promote(r, ab))
    case TApp(f, a) => TApp(promote(f, ab), promote(a, ab))
    case TLambda(k, b) => TLambda(k, promote(b, ab + 1))
  }

  def subst(t: HMonoType, m: Seq[HMonoType]): HMonoType = t match {
    case TVar(i) => if(i <= m.length) m(i-1) else throw new TypeInferenceException("unbound variable: " + i)
    case TArr(l, r) => TArr(subst(l, m), subst(r, m))
    case TApp(f, a) => TApp(subst(f, m), subst(a, m))
    case TLambda(k, b) => TLambda(k, subst(b, TVar(1) +: (m map (l => promote(l)))))
  }

  def beta(t: HMonoType): HMonoType = t match {
    case TApp(TLambda(k, b), u) => {
      val m = for(i <- 1 to b.freeIdx) yield TVar(i)
      beta(subst(b, u +: m))
    }
    case _ => t
  }

  def canonicalOrder(t: HMonoType): Seq[Int] = t match {
    case TVar(i) => Seq(i)
    case TArr(l, r) => {
      val col = canonicalOrder(l)
      val cor = canonicalOrder(r)
      col ++ cor.filter(k => !col.contains(k))
    }
    case TApp(f, a) => {
      val cof = canonicalOrder(f)
      val coa = canonicalOrder(a)
      cof ++ coa.filter(k => !cof.contains(k))
    }
    case TLambda(k, b) => canonicalOrder(b) map (k => k - 1) filter (k => k > 0)
  }

  def canonicalize(t: HMonoType): HMonoType = {
    val co = canonicalOrder(t)
    val m: mutable.Seq[HMonoType] = mutable.Seq((for(i <- 1 to t.freeIdx) yield null):_*)
    for(i <- 1 to co.length) {
      m(co(i-1)-1) = TVar(i)
    }
    subst(t, m)
  }
}

class TypeInference {
  import TypeInference._

  var freshIdx: Int = 0
  val constraints = mutable.Stack[(HMonoType, HMonoType)]()


  def fresh: HMonoType = {
    freshIdx += 1
    TVar(freshIdx)
  }

  def constraintsOf(e: HExpr): HMonoType = {
    if(freshIdx != 0) throw new IRValidationException()
    freshIdx = e.freeTypeIdx
    constraintsOf(e, Seq())
  }

  def constraintsOf(e: HExpr, ctx: Seq[HMonoType]): HMonoType = e match {
    case EVar(i) => if(i <= ctx.length) ctx(i-1) else throw new TypeInferenceException("unbound variable: " + i)
    case ELambda(b) => {
      val tf = fresh
      val trv = constraintsOf(b, tf +: ctx)
      tf --> trv
    }
    case EApp(e1, e2) => {
      val t1 = constraintsOf(e1, ctx)
      val t2 = constraintsOf(e2, ctx)
      val tf = fresh
      constraints.push((t2 --> tf, t1))
      tf
    }
    case ETApp(e, t) => {
      val te = constraintsOf(e, ctx)
      beta(TApp(te, t))
    }
    case x: EPrimitive => {
      val tfi = x.htype.freeIdx
      val m: Seq[HMonoType] = for(i <- (freshIdx + 1) to (freshIdx + tfi)) yield TVar(i)
      freshIdx += tfi
      subst(x.htype, m)
    }
  }

  object TVarEx {
    def unapply(c:(HMonoType, HMonoType)):Option[(Int, HMonoType)] = c match {
      case (TVar(i), t) => Some (i, t)
      case (t, TVar(i)) => Some (i, t)
      case _ => None
    }
  }

  def solve: Seq[HMonoType] = {
    val acc: mutable.Seq[HMonoType] = mutable.Seq((for(k <- 1 to freshIdx) yield TVar(k)):_*)
    while(constraints.size > 0) {
      val c = constraints.pop()
      c match {
        case (t1, t2) if t1 == t2 => 
        case TVarEx(i, t) if !occurs(t, i) => {
          val tm = for(k <- 1 to freshIdx) yield {
            if(k <= i) TVar(k)
            else TVar(k - 1)
          }
          val m = for(k <- 1 to freshIdx) yield {
            if(k < i) TVar(k)
            else if(k == i) subst(t, tm)
            else TVar(k - 1)
          }
          freshIdx -= 1
          constraints.transform{case (ta, tb) => (subst(ta, m), subst(tb, m))}
          acc.transform(t => subst(t, m))
        }
        case (TArr(l1, r1), TArr(l2, r2)) => {
          constraints.push((l1, l2))
          constraints.push((r1, r2))
        }
        case (TApp(f1, a1), TApp(f2, a2)) => {
          constraints.push((f1, f2))
          constraints.push((a1, a2))
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

