package ppl.ltc.ir

import scala.collection._

sealed trait HExprAnnot {
}

case class AVar(idx: Int) extends HExprAnnot { if(idx <= 0) throw new IRValidationException() }
case class AApp(fx: HExprAnnot, arg: HExprAnnot) extends HExprAnnot
case class ATApp(fx: HExprAnnot, arg: HMonoType) extends HExprAnnot
case class ALambda(dom: HMonoType, body: HExprAnnot) extends HExprAnnot
case class ATLambda(dom: HKind, body: HExprAnnot) extends HExprAnnot
case class APrimitive(e: EPrimitive) extends HExprAnnot
case class AAll(dom: HKind, body: HExprAnnot) extends HExprAnnot
case class ATAll(body: HExprAnnot) extends HExprAnnot

