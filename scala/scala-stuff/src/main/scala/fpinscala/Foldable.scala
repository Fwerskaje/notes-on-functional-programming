package fpinscala

import Monoids._
import Fun._

object Foldable {

  trait Foldable[F[_]] {
    def foldMap[A, B](as: F[A])(f: A ⇒ B)(mb: Monoid[B]): B
    def foldRight[A, B](as: F[A])(z: B)(f: A ⇒ B ⇒ B): B
   // def foldLeft[A, B](as: F[A])(z: B)(f: B ⇒ A ⇒ B): B
  }

  def listFoldable[A, B] = new Foldable[List] {

    def foldMap[A, B](as: List[A])(f: A ⇒ B)(mb: Monoid[B]): B = as match {
      case Nil ⇒ mb.zero
      case x :: xs ⇒ mb.op(f(x), foldMap(xs)(f)(mb))
    }

    def foldRight[A, B](as: List[A])(z: B)(f: A ⇒ B ⇒ B): B =
      foldMap(as)((x: A) ⇒ Endo(f(x)))(endoMonoid).appEndo(z)

   // def foldLeft[A, B](as: List[A])(z: B)(f: B => A => B): B =
   //   foldRight(as)(z)(flip(f))

  }

  //scala> Foldable.listFoldable.foldMap(List(1,2,3,4,5))(_.toString)(Monoids.stringMonoid)
  //res6: String = 12345

}

