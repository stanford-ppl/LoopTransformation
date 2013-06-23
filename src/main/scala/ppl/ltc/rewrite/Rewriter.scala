package ppl.ltc.rewrite

import scala.collection._

object Rewriter {
  def rewrite(x: HExpr): Set[HExpr] = rewrite(x, mutable.Map()).filter(u => !stronglyRewritable(u))

  def rewrite(x: HExpr, memomap: mutable.Map[HExpr, Set[HExpr]]): Set[HExpr] = {
    if(memomap.contains(x)) return memomap(x)
    val xtype = x.htype
    // create an accumulator set
    val acc: mutable.Set[HExpr] = mutable.Set(x)
    // create a working set
    val working: mutable.Set[HExpr] = mutable.Set(x)
    // define a processing function
    def proc(u: HExpr) {
      if(!(acc contains u)) {
        if(u.htype != xtype) throw new IRValidationException()
        acc += u
        working += u
      }
    }
    // loop over the working set
    while(working.size > 0) {
      val elem = working.head
      working -= elem
      for(r <- rules) {
        proc(r(elem))
      }
      elem match {
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

  def stronglyRewritable(x: HExpr): Boolean = {
    for(r <- rules) {
      if((r.strong)&&(r(x) != x)) return true
    }
    x match {
      case ELambda(d, u) => stronglyRewritable(u)
      case ETLambda(d, u) => stronglyRewritable(u)
      case EApp(f, a) => stronglyRewritable(f) || stronglyRewritable(a)
      case ETApp(f, a) => stronglyRewritable(f)
      case _ => false
    }
  }

  def rules: Seq[RewriteRule] = Seq(RRComposeAssocLeft, RRComposeAssocRight, RRFMapFusion, RRFMapDeFusion, 
    RRNTransCommLeft, RRNTransCommRight, RRComposeIdentity, RRMapFoldFusion)
}

trait RewriteRule {
  def apply(x: HExpr): HExpr
  val strong: Boolean = false
}

object fmap {
  def unapply(x: HExpr): Option[Tuple4[HType, HType, HType, HExpr]] = x match {
    case EApp(ETApp(ETApp(ETApp(EPFMap, f), l), r), u) => Some((f, l, r, u))
    case _ => None
  }
}

object RRComposeAssocLeft extends RewriteRule {
  def apply(x: HExpr): HExpr = x match {
    case f ∘ (g ∘ h) => (f ∘ g) ∘ h
    case _ => x
  }
  override val strong: Boolean = true
}

object RRComposeAssocRight extends RewriteRule {
  def apply(x: HExpr): HExpr = x match {
    case (f ∘ g) ∘ h => f ∘ (g ∘ h)
    case _ => x
  }
}

object RRFMapFusion extends RewriteRule {
  def apply(x: HExpr): HExpr = x match {
    case (fmap(f, lf, rf, u) ∘ fmap(g, lg, rg, v)) if ((f == g)&&(rg == lf)) =>
        EPFMap(f)(lg)(rf)(u ∘ v)
    case _ => x
  }
}

object RRFMapDeFusion extends RewriteRule {
  def apply(x: HExpr): HExpr = x match {
    case fmap(f, l, r, u ∘ v) => {
      u.htype match {
        case ul --> ur => EPFMap(f)(ul)(r)(u) ∘ EPFMap(f)(l)(ul)(v)
      }
    }
    case _ => x
  }
}

object RRNTransCommLeft extends RewriteRule {
  def apply(x: HExpr): HExpr = x match {
    case fmap(h, lf, rf, u) ∘ ETApp(n, v) if (lf == v) => n.htype.beta match {
      case TLambda(KType, TArr(TApp(f, TVar(1, KType)), TApp(g, TVar(1, KType)))) if(g == h) => {
        n(rf) ∘ EApp(ETApp(ETApp(ETApp(EPFMap, f), lf), rf), u)
      }
    }
    case _ => x
  }
}

object RRNTransCommRight extends RewriteRule {
  def apply(x: HExpr): HExpr = x match {
    case ETApp(n, v) ∘ fmap(h, lf, rf, u) if (rf == v) => n.htype.beta match {
      case TLambda(KType, TArr(TApp(f, TVar(1, KType)), TApp(g, TVar(1, KType)))) if(f == h) => {
        EApp(ETApp(ETApp(ETApp(EPFMap, g), lf), rf), u) ∘ n(lf)
      }
    }
    case _ => x
  }
}

object RRComposeIdentity extends RewriteRule {
  def apply(x: HExpr): HExpr = x match {
    case f ∘ ETApp(Primitives.identity, a) => f
    case ETApp(Primitives.identity, a) ∘ f => f
    case _ => x
  }
  override val strong: Boolean = true
}

object RRMapFoldFusion extends RewriteRule {
  def apply(x: HExpr): HExpr = x match {
    case EApp(EApp(ETApp(ETApp(ETApp(EPFold, f), a), b), v), w) ∘ fmap(g, l, r, u) if((f == g)&&(r == a)) =>
      EApp(EApp(ETApp(ETApp(ETApp(EPFold, f), l), b), v ∘ u), w)
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
