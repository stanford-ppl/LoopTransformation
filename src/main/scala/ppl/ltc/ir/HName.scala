package ppl.ltc.ir


sealed trait HName {
  override def toString: String = this match {
    case HNameS(n) => n
    case HNameSI(n, i) => n + "_" + i.toString
    case HNameI(i) => "__" + i.toString
  }
}

case class HNameS(name: String) extends HName {
  if(name contains "_") throw new IRValidationException()
}
case class HNameSI(name: String, index: Int) extends HName {
  if(name contains "_") throw new IRValidationException()
}
case class HNameI(index: Int) extends HName

