import scalaz._
import Scalaz._
import scalaz.syntax

case class TrafficLight(name: String)
val red = TrafficLight("red")
val yellow = TrafficLight("yellow")
val green = TrafficLight("green")

implicit val TrafficLightEqual: Equal[TrafficLight] = Equal.equal(_ == _)

red ≟ green

(1 to 5).toList >>= {x: Int ⇒ List(x + 1, x, x - 1)}
