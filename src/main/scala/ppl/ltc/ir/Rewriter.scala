package ppl.ltc.ir

// peephole rewriter
object Rewriter {
  def rewrite(x: HExpr): HExpr = {
    for(p <- primitives) {
      if(x == p) return p
    }
    for(r <- rules) {
      val rax = r(x)
      if(rax != x) return rewrite(rax)
    }
    x match {
      case ELambda(n, u) => {
        val ru = rewrite(u)
        if(ru == u) {
          x
        }
        else {
          rewrite(ELambda(n, ru))
        }
      }
      case EApply(f, a) => {
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
