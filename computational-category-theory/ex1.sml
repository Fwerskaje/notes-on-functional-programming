datatype Colour = red | blue | green

fun warm(red) = true
  | warm(blue) = false
  | warm(green) = false 

datatype Plant =
	 flower  of string * int * colour
       | foliage of string * int 

fun height(flower(_, n, _)) = n
  | height(foliage(_, n)) = n 

datatype Num = zero | succ of Num

fun even(zero) = true
  | even(succ(n)) = not (even n)

fun add(zero, n) = n
  | add((succ k), n) = succ (add(k, n))  

abstype Mixture = mix of int * int * int with
val cement = mix(6, 0, 0)
and sand = mix(0, 6, 0)
fun succMix(mix(x, y, z)) = mix(x + 1, y + 1, z + 1)
end

fun sign(n) = n > 0

fun absvalue(n) =
    case sign n of
        true => n
      | false => ~n

fun fib(0) = 0
  | fib(1) = 1 
  | fib(n) = fib(n - 1) + fib(n - 2) 

fun numprint(zero) = 0
  | numprint(succ n) = 1 + numprint(n) 
