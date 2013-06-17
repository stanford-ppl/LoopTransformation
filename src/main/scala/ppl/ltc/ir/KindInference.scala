package ppl.ltc.ir

import scala.collection._


class KindInferenceException(msg: String) extends Exception(msg)

object KindInference {
  def occurs(k: HKind, id: Int): Boolean = k match {
    case KVar(i) => (i == id) 
    case KArr(l, r) => occurs(l, id) || occurs(r, id)
    case _ => false
  }

  def subst(t: HKind, m: Seq[HKind]): HKind = t match {
    case KVar(i) => if(i <= m.length) m(i-1) else throw new KindInferenceException("unbound variable: " + i)
    case KArr(l, r) => KArr(subst(l, m), subst(r, m))
    case KType => KType
  }
}

class KindInference {
  import KindInference._

  var freshIdx: Int = 0
  val constraints = mutable.Stack[(HKind, HKind)]()


  def fresh: HKind = {
    freshIdx += 1
    KVar(freshIdx)
  }

  def constraintsOf(t: HMonoType): HKind = {
    if(freshIdx != 0) throw new IRValidationException()
    freshIdx = t.freeIdx
    constraintsOf(t, for(i <- 1 to freshIdx) yield KVar(i))
  }

  def constraintsOf(t: HMonoType, ctx: Seq[HKind]): HKind = t match {
    case TVar(i) => if(i <= ctx.length) ctx(i-1) else throw new KindInferenceException("unbound variable: " + i)
    case TLambda(d, b) => {
      val krv = constraintsOf(b, d +: ctx)
      KArr(d, krv)
    }
    case TApp(t1, t2) => {
      val k1 = constraintsOf(t1, ctx)
      val k2 = constraintsOf(t2, ctx)
      val kf = fresh
      constraints.push((KArr(k2, kf), k1))
      kf
    }
    case TArr(l, r) => {
      constraints.push((KType, constraintsOf(l, ctx)))
      constraints.push((KType, constraintsOf(r, ctx)))
      KType
    }
  }

  object KVarEx {
    def unapply(c:(HKind, HKind)):Option[(Int, HKind)] = c match {
      case (KVar(i), k) => Some (i, k)
      case (k, KVar(i)) => Some (i, k)
      case _ => None
    }
  }

  lazy val solution: mutable.Seq[HKind] = mutable.Seq((for(k <- 1 to freshIdx) yield KVar(k)):_*)
  def solve: Seq[HKind] = {
    solution
    while(constraints.size > 0) {
      solveStep()
    }
    solution
  }

  def solveStep() {
    val c = constraints.pop()
    c match {
      case (t1, t2) if t1 == t2 => 
      case KVarEx(i, t) if !occurs(t, i) => {
        val mt = for(k <- 1 to freshIdx) yield {
          if(k <= i) KVar(k)
          else KVar(k - 1)
        }
        val m = for(k <- 1 to freshIdx) yield {
          if(k < i) KVar(k)
          else if(k == i) subst(t, mt)
          else KVar(k - 1)
        }
        freshIdx -= 1
        constraints.transform{case (ta, tb) => (subst(ta, m), subst(tb, m))}
        solution.transform(t => subst(t, m))
      }
      case (KArr(l1, r1), KArr(l2, r2)) => {
        constraints.push((l1, l2))
        constraints.push((r1, r2))
      }
      case _ => throw new TypeInferenceException("could not unify constraint: " + c.toString)
    }
  }
}