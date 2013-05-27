name := "looptransformation"

scalacOptions += "-deprecation"

initialCommands in console := "import ppl.ltc.ir._; import ScalaEmbedding._"

libraryDependencies ++= Seq(
  "org.scalatest" %% "scalatest" % "1.6.1" % "test"
)
