package ppl.ltc.ir

import scala.collection.immutable.Seq

sealed trait HMType {
  /* the number of qualified type variables appearing in this expression */ 
  val tarity: Int
  /* specialize this type */
  def specialize(op: HMSpecialization): HMType
  /* helper method to construct a function type */
  def -->(r: HMType): HMType = {
    if(r.tarity != this.tarity) throw new IRValidationException()
    HMTApply(tarity, HMTPFunction, Seq(this, r))
  }
  /* format this type, without binding variables */
  def format: String
  /* give the description of this type */
  override def toString: String = {
    var acc: String = ""
    for(i <- 0 until tarity) {
      acc += "∀" + (0x03B1 + i).toChar.toString + ". "
    }
    acc + format
  }
}

/* function type unapplicator */
object --> {
  def unapply(t: HMType): Option[Tuple2[HMType, HMType]] = t match {
    case HMTApply(ta, HMTPFunction, Seq(td, tc)) => Some((td, tc))
    case _ => None
  }
}

/* type specialization */
case class HMSpecialization(val tarity: Int, val subs: Seq[HMType]) {
  for(s <- subs) {
    if(s.tarity != tarity) throw new IRValidationException()
  }
}

/* type application */
case class HMTApply(val tarity: Int, val primitive: HMTypePrimitive, val args: Seq[HMType]) extends HMType {
  if(args.length != primitive.parity) throw new IRValidationException()
  for(a <- args) {
    if(a.tarity != tarity) throw new IRValidationException()
  }
  def specialize(op: HMSpecialization): HMType = HMTApply(op.tarity, primitive, args map (a => a.specialize(op)))
  def format: String = {
    primitive.format(args map (h => h.format))
  }
}

/* the vidx-th qualified type variable */
case class HMTVariable(val tarity: Int, val vidx: Int) extends HMType {
  if((vidx < 0)||(vidx >= tarity)) throw new IRValidationException()
  def specialize(op: HMSpecialization): HMType = op.subs(vidx)
  def format: String = {
    (0x03B1 + vidx).toChar.toString
  }
}


