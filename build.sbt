name := "looptransformation"

scalaVersion := "2.10.1"

scalacOptions += "-deprecation"

scalacOptions += "-feature"

initialCommands in console := "import ppl.ltc.rewrite._; import ScalaEmbedding._"

libraryDependencies ++= Seq(
  "org.scalatest" %% "scalatest" % "1.9.1" % "test"
)

resolvers ++= Seq(
  "Sonatype Snapshots" at "http://oss.sonatype.org/content/repositories/snapshots",
  "Sonatype Releases" at "http://oss.sonatype.org/content/repositories/releases"
)

libraryDependencies ++= Seq(
  "org.scalacheck" %% "scalacheck" % "1.10.1" % "test"
)
