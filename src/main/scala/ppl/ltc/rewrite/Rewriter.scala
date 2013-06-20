package ppl.ltc.rewrite

import scala.collection._

object Rewriter {
  def rewrite(x: HExpr): Set[HExpr] = rewrite(x, mutable.Map())

  def rewrite(x: HExpr, memomap: mutable.Map[HExpr, Set[HExpr]]): Set[HExpr] = {
    if(memomap.contains(x)) return memomap(x)
    // create an accumulator set
    val acc: mutable.Set[HExpr] = mutable.Set(x)
    // create a working set
    val working: mutable.Set[HExpr] = mutable.Set(x)
    // define a processing function
    def proc(u: HExpr) {
      if(!(acc contains u)) {
        acc += u
        working += u
      }
    }
    // loop over the working set
    while(working.size > 0) {
      val elem = working.head
      working -= elem
      for(r <- rules) {
        proc(r(x))
      }
      val rsx = elem match {
        case ELambda(d, u) => {
          for(w <- rewrite(u, memomap)) {
            proc(ELambda(d, w))
          }
        }
        case ETLambda(d, u) => {
          for(w <- rewrite(u, memomap)) {
            proc(ETLambda(d, w))
          }
        }
        case EApp(f, a) => {
          val rf = rewrite(f, memomap)
          val ra = rewrite(a, memomap)
          for(wf <- rf) {
            for(wa <- ra) {
              proc(EApp(wf, wa))
            }
          }
        }
        case ETApp(f, a) => {
          for(w <- rewrite(f, memomap)) {
            proc(ETApp(w, a))
          }
        }
        case _ => 
      }
    }
    // store the result in the memoization map
    memomap(x) = acc
    // and return
    acc
  }

  def rules: Seq[RewriteRule] = Seq(RRComposeAssocLeft, RRComposeAssocRight)
}

trait RewriteRule {
  def apply(x: HExpr): HExpr
}

object RRComposeAssocLeft extends RewriteRule {
  def apply(x: HExpr): HExpr = x match {
    case f ∘ (g ∘ h) => (f ∘ g) ∘ h
    case _ => x
  }
}

object RRComposeAssocRight extends RewriteRule {
  def apply(x: HExpr): HExpr = x match {
    case (f ∘ g) ∘ h => f ∘ (g ∘ h)
    case _ => x
  }
}

/*
object RRConst extends RewriteRule {
  def apply(x: HExpr): HExpr = x match {
    case ELambda(n, u) if !u.occurs(n) => EApply(Functions.const, u)
    case _ => x
  }
}

object RRCompose extends RewriteRule {
  def apply(x: HExpr): HExpr = x match {
    case ELambda(n, EApply(f, u)) if !f.occurs(n) => {
      EApply(EApply(Functions.compose, f), ELambda(n, u))
    }
    case _ => x
  }
}

object RRIdentity extends RewriteRule {
  def apply(x: HExpr): HExpr = x match {
    case ELambda(n, EVar(m)) if (n == m) => Functions.identity
    case _ => x
  }
}

object RRComposeIdentity extends RewriteRule {
  def apply(x: HExpr): HExpr = x match {
    case Functions.identity ∘ a => a
    case a ∘ Functions.identity => a
    case _ => x
  }
}

// ezyang: I think what we want to do is unfuse all fmaps before
// re-fusing them, since a composition of completely point-wise fmaps
// is a canonical form in some sense
object RRFmapFusion extends RewriteRule {
  def apply(x: HExpr): HExpr = x match {
    case EApply(EFmap(f1), x1) ∘ EApply(EFmap(f2), x2) if (f1 == f2) => {
      EApply(EFmap(f1), x1 ∘ x2)
    }
    case _ => x
  }
}

object RRComposeAssocRight extends RewriteRule {
  def apply(x: HExpr): HExpr = x match {
    case (f ∘ g) ∘ h => f ∘ (g ∘ h)
    case _ => x
  }
}
*/
