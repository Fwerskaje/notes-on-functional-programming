import scalaz._
import Scalaz._

val f = (_: Int) * 5
val g = (_: Int) + 3

(g ∘ f)(8) // 55

val k = {(_: Int) * 2} ⊛ {(_: Int) + 10} ⊛ {(_: Int) - 4}
val k2 = k {_ + _ * _}
k2(5) // 25

1.some *> Applicative[Option].point(3)
