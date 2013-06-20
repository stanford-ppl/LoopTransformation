package ppl.ltc.rewrite

import scala.collection._

object Rewriter {
  def rewrite(x: HExpr): Set[HExpr] = {
    // create an accumulator set
    val acc: mutable.Set[HExpr] = Set(x)
    // try all the rules on x
    for(r <- rules) {
      val rax = r(x)
      if(rax != x) return rewrite(rax)
    }
    // try to rewrite components of the expression
    val rv = x match {
      case ELambda(d, u) => ELambda(d, rewrite(u))
      case ETLambda(d, u) => ETLambda(d, rewrite(u))
      case EApp(f, a) => EApp(rewrite(f), rewrite(a))
      case ETApp(f, a) => ETApp(rewrite(f), a)
      case _ => x
    }
    if(rv == x) {
      x
    }
    else {
      rewrite(rv)
    }
  }

  def rules: Seq[RewriteRule] = Seq(RRComposeAssocLeft)
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
