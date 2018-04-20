import scalaz._
import Scalaz._

object Nat {

  import scala.annotation.tailrec

  sealed trait Nat
  case class Z() extends Nat
  case class S(n: Nat) extends Nat

  private def add(x: Nat, y: Nat): Nat = {
    @tailrec
    def go(x: Nat, acc: Nat): Nat = x match {
      case Z() => acc
      case S(n) => go(n, S(acc))
    }
    go(x,y)
  }

  private def toInt(x: Nat): Int = {
    @tailrec
    def go(x: Nat, acc: Int): Int = x match {
      case Z() => acc
      case S(n) => go(n, acc + 1)
    }
    go(x, 0)
  }

  @tailrec
  private def eqNat(x: Nat, y: Nat): Boolean = (x, y) match {
    case (S(n), Z()) => false
    case (Z(), S(n)) => false
    case (Z(), Z()) => true
    case (S(n), S(k)) => eqNat(n, k)
  }

  private def toNat(x: Int): Nat = {
    @tailrec
    def go(acc: Nat, x: Int): Nat =
      if (x == 0) acc else go(S(acc), x - 1)
    go(Z(), x)
  }

  /*
  implicit object NatInstances extends Semigroup[Nat]
      with Monoid[Nat]
      with Show[Nat]
      with Equal[Nat] {

    def zero = Z()
    def append(f1: Nat, f2: => Nat): Nat = add(f1, f2)

    override def shows(n: Nat) = toInt(n).shows

    def equal(a1: Nat, a2: Nat): Boolean = eqNat(a1, a2)

  }*/

}

object Ex1 {

  import Nat._
  

  case class Sum[A](getSum: A)

  implicit object SumIntInstances extends Semigroup[Sum[Int]] with Monoid[Sum[Int]] {
    def zero = Sum(0)
    def append(f1: Sum[Int], f2: => Sum[Int]) = Sum(f1.getSum + f2.getSum)
  }

  val s1 = Sum(42)
  val s2 = Sum(36)
  val s3 = s1 |+| s2
  //val s4 = NatInstances.equal(Z(), S(S(Z()))) // hm~


}
