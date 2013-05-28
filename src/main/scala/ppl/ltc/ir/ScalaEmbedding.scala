package ppl.ltc.ir

import scala.language.implicitConversions

object ScalaEmbedding {
  class SCESym(val s: String)

  implicit def sym2hname(y: SCESym): HName = HNameS(y.s)
  implicit def sym2hexpr(y: SCESym): HExpr = EVar(HNameS(y.s))

  val a = new SCESym("a")
  val b = new SCESym("b")
  val c = new SCESym("c")
  val d = new SCESym("d")
  val e = new SCESym("e")
  val f = new SCESym("f")
  val g = new SCESym("g")
  val h = new SCESym("h")
  val i = new SCESym("i")
  val j = new SCESym("j")
  val k = new SCESym("k")
  val l = new SCESym("l")
  val m = new SCESym("m")
  val n = new SCESym("n")
  val o = new SCESym("o")
  val p = new SCESym("p")
  val q = new SCESym("q")
  val r = new SCESym("r")
  val s = new SCESym("s")
  val t = new SCESym("t")
  val u = new SCESym("u")
  val v = new SCESym("v")
  val w = new SCESym("w")
  val x = new SCESym("x")
  val y = new SCESym("y")
  val z = new SCESym("z")

}

