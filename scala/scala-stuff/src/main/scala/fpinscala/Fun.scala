package fpinscala

object Fun {
  def flip[A, B, C]: (A ⇒ B ⇒ C) ⇒ B ⇒ A ⇒ C = f ⇒ x ⇒ y ⇒ f(y)(x)
}