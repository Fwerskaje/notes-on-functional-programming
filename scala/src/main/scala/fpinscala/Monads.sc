import scalaz._
import Scalaz._

val f = Kleisli.kleisli[Option, Int, Int](x ⇒ (x + 1).some)

val g = Kleisli.kleisli[Option, Int, Int](x ⇒ (x * 100).some)

4.some >>= (f <=< g)

4.some >>= (f >=> g)

val addStuff: Reader[Int, Int] = for {
  a ← Reader {(_: Int) * 2}
  b ← Reader {(_: Int) + 10}
} yield a + b

addStuff(3)
