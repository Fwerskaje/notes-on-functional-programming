import fpinscala.Monoids._

val endoSucc = endoMonoid.op(Endo({(_: Int) + 1}), Endo({(_: Int) * 3}))
endoSucc.appEndo(3)

