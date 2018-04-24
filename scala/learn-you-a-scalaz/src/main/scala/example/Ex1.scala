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

}

object Ex1 {

  case class Sum[A](getSum: A)

  
  implicit object SumIntInstances extends Semigroup[Sum[Int]] with Monoid[Sum[Int]] {
    def zero = Sum(0)
    def append(f1: Sum[Int], f2: => Sum[Int]) = Sum(f1.getSum + f2.getSum)
  } 

  implicit def sumEquals[A]: Equal[Sum[A]] = new Equal[Sum[A]] {
    def equal(a1: Sum[A], a2: Sum[A]): Boolean = a1 == a2
  }

  implicit val sumFunctor: Functor[Sum] = new Functor[Sum] {
    def map[A,B](fa: Sum[A])(f: A => B): Sum[B] = Sum(f(fa.getSum))
  }

  implicit val sumApplicative: Applicative[Sum] = new Applicative[Sum] {
    def point[A](a: => A): Sum[A] = Sum(a)
    def ap[A, B](fa: => Sum[A])(f: => Sum[A => B]): Sum[B] = Sum(f.getSum(fa.getSum))
  }

  val s1 = (42.point[Sum] <*> {(_: Int) + 1}.point[Sum]) |+| 42.point[Sum]

}
