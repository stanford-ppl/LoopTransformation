name := "looptransformation"

scalaVersion := "2.10.1"

scalacOptions += "-deprecation"

scalacOptions += "-feature"

initialCommands in console := "import ppl.ltc.ir._; import ScalaEmbedding._"

libraryDependencies ++= Seq(
  "org.scalatest" %% "scalatest" % "1.9.1" % "test"
)
