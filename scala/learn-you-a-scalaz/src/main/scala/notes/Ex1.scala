object Exp1 {

  val maybe = Option(("hello", "world"))

  val res0 = for {
    entry <- maybe
    (first, _) = entry
  } yield first


}

