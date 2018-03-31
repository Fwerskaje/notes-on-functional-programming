import Dependencies._

lazy val root = (project in file(".")).
  settings(
    inThisBuild(List(
      organization := "com.example",
      scalaVersion := "2.12.5",
      version      := "0.1.0-SNAPSHOT"
    )),
    name := "learn-you-a-scalaz",
    libraryDependencies += "org.scalaz" %% "scalaz-core" % "7.3.0-M21"
  )
