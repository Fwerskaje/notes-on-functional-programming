import fpinscala.Foldable._
import fpinscala.Monoids._

listFoldable.foldRight(List(1,2,3,4,5))(1)(((_: Int) * (_: Int)).curried)