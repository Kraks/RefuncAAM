import Dependencies._

lazy val root = (project in file(".")).
  settings(
    inThisBuild(List(
      organization := "gnw",
      scalaVersion := "2.11.2",
      version      := "0.1.0-SNAPSHOT"
    )),
    name := "refuncAAM",
    libraryDependencies += scalaTest % Test,
    autoCompilerPlugins := true,
    addCompilerPlugin("org.scala-lang.plugins" % "scala-continuations-plugin_2.11.2" % "1.0.2"),
    libraryDependencies += "org.scala-lang.plugins" % "scala-continuations-library_2.11" % "1.0.2",
    scalacOptions += "-P:continuations:enable"
  )
