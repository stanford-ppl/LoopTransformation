package ppl.ltc.ir

sealed trait Polarity {
  def lub(x: Polarity): Polarity = (this, x) match {
    case (_, Unspecified) => Unspecified
    case (Unspecified, _) => Unspecified
    case (Positive, Negative) => Unspecified
    case (Negative, Positive) => Unspecified
    case (Positive, _) => Positive
    case (Negative, _) => Negative
    case (Constant, z) => z
  }
  def unary_-() = this match {
    case Unspecified => Unspecified
    case Positive => Negative
    case Negative => Positive
    case Constant => Constant
  }
  def *(x: Polarity) = (this, x) match {
    case (Constant, _) => Constant
    case (_, Constant) => Constant
    case (Unspecified, _) => Unspecified
    case (_, Unspecified) => Unspecified
    case (Positive, Positive) => Positive
    case (Negative, Positive) => Negative
    case (Positive, Negative) => Negative
    case (Negative, Negative) => Negative
  }
}

object Unspecified extends Polarity
object Positive extends Polarity
object Negative extends Polarity
object Constant extends Polarity


