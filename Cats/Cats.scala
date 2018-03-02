import cats._
import cats.implicits._

object ex1 {

  val showInt = Show.apply[Int]
  val showString = Show.apply[String]

  val intAsString = showInt.show(123)
  val stringAsString = showString.show("abc")

}

object ex2 {

  import java.util.Date

  val showInt = 42.show

  /*
  implicit val dateShow: Show[Date] =
    new Show[Date] {
      def show(date: Date): String =
        s"${date.getTime} ms since the epoch."
    } */

  implicit val dateShow: Show[Date] =
    Show.show(date => s"${date.getTime} ms since the epoch.")

  val t = new java.util.Date
  val timeString = t.show

  implicit val dateEq: Eq[Date] =
    Eq.instance[Date] { (date1, date2) =>
      date1.getTime === date2.getTime
    }

  lazy val x = {
    val n1 = new Date
    Thread.sleep(1)
    val n2 = new Date
    n1 === n2
  }

}

object Cat {

  final case class Cat(name: String, age: Int, color: String)

  implicit val catEq: Eq[Cat] =
    Eq.instance[Cat] { (cat1, cat2) =>
      (cat1.name, cat1.age, cat1.color) === (cat2.name, cat2.age, cat2.color)
    }

  val cat1 = Cat("Garfield", 38, "orange and black")
  val cat2 = Cat("Heathcliff", 33, "orange and black")

  val optionCat1 = Option(cat1)
  val optionCat2 = Option.empty[Cat]

}

object ex3 {

  val monoidString = "Hello, " |+| "there!"

  val map1 = Map("a" -> 1, "b" -> 2)
  val map2 = Map("b" -> 3, "d" -> 4)

  val map3 = map1 |+| map2

  val tuple1 = ("hello", 123)
  val tuple2 = ("world", 321)

  val tuple3 = tuple1 |+| tuple2

}
