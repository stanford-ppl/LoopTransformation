package ppl.ltc.ir

import scala.collection._


sealed trait HExpr {
  override def toString: String = PrettyPrint.pprint(this)
  def freeIdx: Int = {
    import scala.math.max
    this match {
      case EVar(i) => i
      case EApp(f, a) => max(f.freeIdx, a.freeIdx)
      case ETApp(f, a) => f.freeIdx
      case ELambda(b) => b.freeIdx - 1
      case x: EPrimitive => 0
    }
  }
  def freeTypeIdx: Int = {
    import scala.math.max
    this match {
      case EVar(i) => 0
      case EApp(f, a) => max(f.freeTypeIdx, a.freeTypeIdx)
      case ETApp(f, a) => max(f.freeTypeIdx, a.freeIdx)
      case ELambda(b) => b.freeTypeIdx
      case x: EPrimitive => 0
    }
  }
}

case class EVar(idx: Int) extends HExpr { if(idx <= 0) throw new IRValidationException() }
case class EApp(fx: HExpr, arg: HExpr) extends HExpr
case class ETApp(fx: HExpr, arg: HMonoType) extends HExpr
case class ELambda(body: HExpr) extends HExpr

sealed trait EPrimitive extends HExpr {
  val name: String
  val htype: HMonoType
}

object EFMap extends EPrimitive {
  val name: String = "fmap"
  val htype: HMonoType = TLambda(KArr(KType, KType), (TVar(2) --> TVar(3)) --> (TApp(TVar(1), TVar(2)) --> TApp(TVar(1), TVar(3))))
}

/* things we may want */
// case class ETyped(type: HMonoType, body: HExpr) extends HExpr
// case class EExists(kind: HKind, body: HExpr) extends HExpr

/*
sealed trait HExpr {
  override def toString: String = PrettyPrint.pprint(this)
  def htype: HType = {
    val ti = new TypeInference
    val ttp = ti.constraintsOf(this, collection.immutable.Map[HName, HType]())
    val tmap = ti.solve
    ttp.subst(tmap).canonicalize
  }
  def occurs(n: HName): Boolean = this match {
    case EVar(m) => n == m
    case ELambda(m, u) => (n != m) && (u.occurs(n))
    case EApply(fx, arg) => fx.occurs(n) || arg.occurs(n)
    case _ => false
  }
  def apply(y: HExpr): HExpr = EApply(this, y)
  def compose(y: HExpr): HExpr = {
    EApply(EApply(Functions.compose, this), y)
  }
  def ∘(y: HExpr): HExpr = this.compose(y)
  def *(y: HExpr): HExpr = this.compose(y)
}

case class EVar(name: HName) extends HExpr
case class ELambda(name: HName, body: HExpr) extends HExpr
case class EApply(fx: HExpr, arg: HExpr) extends HExpr

sealed trait EPrimitive extends HExpr {
  override def toString: String = throw new IRValidationException()
  override def htype: HType = throw new IRValidationException()
}

case class EFmap(f: HFunctor) extends EPrimitive {
  override def toString: String = "fmap{" + f.toString + "}"
  override def htype: HType = {
    val a = TParam(0)
    val b = TParam(1)
    (a --> b) --> (f(a) --> f(b))
  }
}
case class EInt(value: Int) extends EPrimitive {
  override def toString: String = value.toString
  override def htype: HType = DInt()
}
case class EBool(value: Boolean) extends EPrimitive {
  override def toString: String = value.toString
  override def htype: HType = DBool()
}
case class EDouble(value: Double) extends EPrimitive {
  override def toString: String = value.toString
  override def htype: HType = DDouble()
}

case class EFilter(f: HFunctor) extends EPrimitive {
  override def toString: String = "filter{" + f.toString + "}"
  override def htype: HType = {
    val a = TParam(0)
    DProduct(DBool(), a) --> DList(a)
  }
}
case class EZip(f: HFunctorRepresentable) extends EPrimitive {
  override def toString: String = "zip{" + f.toString + "}"
  override def htype: HType = {
    val a = TParam(0)
    val b = TParam(1)
    f(a) --> (f(b) --> f(DProduct(a, b)))
  }
}
*/
