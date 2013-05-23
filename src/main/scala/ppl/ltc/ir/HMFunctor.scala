package ppl.ltc.ir

import scala.collection.immutable.Seq
import scala.collection.immutable.Map


sealed trait HMFunctor extends HMHasTypeVars[HMFunctor] {
  def apply(t: HMType): HMType
}

