package fpinscala

object Monad {

  import fpinscala.Functor._

  trait Monad[M[_]] extends Functor[M] {
    def unit[A](a: ⇒ A): M[A]

    def flatMap[A, B](ma: M[A])(f: A ⇒ M[B]): M[B]

    def map[A, B](ma: M[A])(f: A ⇒ B): M[B] = flatMap(ma)(a ⇒ unit(f(a)))

    def map2[A, B, C](ma: M[A], mb: M[B])(f: (A, B) ⇒ C): M[C] =
      flatMap(ma)(a ⇒ map(mb)(b ⇒ f(a, b)))
  }

  case class Id[A](value: A)

  object Id extends Monad[Id] {
    override def flatMap[A, B](ma: Id[A])(f: A => Id[B]): Id[B] = f(ma.value)
    override def unit[A](a: => A): Id[A] = Id(a)
  }

}