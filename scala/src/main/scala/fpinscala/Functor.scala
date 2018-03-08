package fpinscala

object Functor {

  trait Functor[F[_]] {
    def map[A, B](fa: F[A])(f: A ⇒ B): F[B]
  }

  object listFunctor extends Functor[List] {
    def map[A,B](as: List[A])(f: A => B): List[B] = as map f
  }

}
