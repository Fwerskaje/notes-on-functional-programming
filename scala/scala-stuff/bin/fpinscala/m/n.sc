2 + 2 * 2
// 1 byte = 1 bit * 8

trait B {
  def toBit: Bit
}

case class Bit(n: Int) extends B {
  def ==(b: B): Boolean = b.toBit.n == n
  def toBit: Bit = this
}

case class Byte(n: Int) extends B {
  def ==(b: Bit): Boolean = this.toBit == b
  def toBit: Bit = Bit(n * 8)
}

println(Bit(8) == Bit(8))
println(Bit(8) == Byte(1))
println(Bit(1) == Byte(1))

/*
true
res1: Unit = ()
true
res2: Unit = ()
false
res3: Unit = ()
 */