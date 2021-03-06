package ppl.ltc.ir

/*
// peephole rewriter

// ezyang: this rewriter doesn't have type information
object Rewriter {
  def rewrite(x: HExpr): HExpr = {
    // if x is primitive, we can't rewrite it
    if(x.isInstanceOf[EPrimitive]) return x
    // try all the rules on x
    for(r <- rules) {
      val rax = r(x)
      if(rax != x) return rewrite(rax)
    }
    // try to rewrite components of the expression
    x match {
      case ELambda(u) => {
        val ru = rewrite(u)
        if(ru == u) {
          x
        }
        else {
          rewrite(ELambda(ru))
        }
      }
      case EApp(f, a) => {
        val rf = rewrite(f)
        val ra = rewrite(a)
        if((rf == f)&&(ra == a)) {
          x
        }
        else {
          rewrite(EApply(rf, ra))
        }
      }
      case _ => x
    }
  }

  def rules: Seq[RewriteRule] = Seq(RRConst, RRCompose, RRIdentity, RRComposeIdentity, RRFmapFusion, RRComposeAssocRight)
  def primitives: Seq[HExpr] = Seq(Functions.const, Functions.compose, Functions.identity)
}

trait RewriteRule {
  def apply(x: HExpr): HExpr
}

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

