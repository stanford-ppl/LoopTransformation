package test

import org.scalatest.FunSuite
import ppl.ltc.ir._

class HTypeTest extends FunSuite {

  test("arrow") {
    expect("α ——> β") { (TParam(0) --> TParam(1)).toString }
  }

}

