package ppl.ltc.rewrite

import scala.language.implicitConversions


class IRValidationException extends Exception

object Util {
  def agree[T >: Null](x: T, y: T): T = {
    if(x == null) y
    else if(y == null) x
    else if(x == y) x
    else throw new IRValidationException()
  }
}

object ScalaEmbedding {
  private var edepth: Int = 0
  private var tdepth: Int = 0

  class SSExpr(val o: Int, val t: HType)
  class SSType(val o: Int, val k: HKind)

  implicit def ssexpr2expr(s: SSExpr): HExpr = EVar(edepth - s.o, s.t)
  implicit def sstype2type(s: SSType): HType = TVar(tdepth - s.o, s.k)

  def tlambda(k: HKind, f: SSType => HType): HType = {
    val s = new SSType(tdepth, k)
    tdepth += 1
    val b = f(s)
    tdepth -= 1
    TLambda(k, b)
  }

  def etlambda(k: HKind, f: SSType => HExpr): HExpr = {
    val s = new SSType(tdepth, k)
    tdepth += 1
    val b = f(s)
    tdepth -= 1
    ETLambda(k, b)
  }

  def elambda(t: HType, f: SSExpr => HExpr): HExpr = {
    val s = new SSExpr(edepth, t)
    edepth += 1
    val b = f(s)
    edepth -= 1
    ELambda(t, b)
  }

  def tnew(): SSType = tnew(KType)
  def tnew(k: HKind): SSType = {
    tdepth += 1
    new SSType(tdepth - 1, k)
  }

  def enew(t: HType): SSExpr = {
    edepth += 1
    new SSExpr(edepth - 1, t)
  }

  def tfree(s: SSType) {
    tdepth -= 1
    if(tdepth != s.o) throw new IRValidationException()
  }

  def efree(s: SSExpr) {
    edepth -= 1
    if(edepth != s.o) throw new IRValidationException()
  }

  def fmap(f: HType)(x: HExpr): HExpr = {
    x.htype match {
      case l --> r => EPFMap(f)(l)(r)(x)
      case _ => throw new IRValidationException()
    }
  }

  def fold(f: HType)(x: HExpr): HExpr = {
    x.htype match {
      case (a --> (b --> c)) if (a == b)&&(a == c) => EPFold(f)(a)(a)(Primitives.identity(a))(x)
      case _ => throw new IRValidationException()
    }
  }

  val ★ = KType
  val functor = ★ -->+ ★
}

