datatype ’a Pair = pair of (’a * ’a)

datatype ’a list = nil | ’a :: (’a list)

fun length nil = 0
  | length (h :: t) = 1 + length t
				 
fun member(e, nil)      = false
  | member(e, (h :: t)) = if e = h then true else member(e, t)
			       
abstype 'a Set = set of 'a list with
			   
val emptyset = set([])
		  
fun is_empty(set(s)) = length(s) = 0
				       
fun singleton(x) = set([x])
		      
fun union(set(s), set(t)) = set(append(s, t))
			       
fun member(x, set(l)) = list_member(x, l)
				   
fun remove(x, set(l)) = set(list_remove(x, l))
			   
fun singleton_split(set(nil))    = raise empty_set
  | singleton_split(set(x :: s)) = (x, remove(x, set(s)))

fun split(s) =
    let val (x, s') = singleton_split(s) in
	(singleton(x) ,s')
    end	       

end

datatype ('o, 'a) Cat =
	 cat of ('a -> 'o) * ('a -> 'o) * ('o -> 'a) * ('a * 'a -> 'a)

datatype 'a Set_Arrow =
	 set_arrow of ('a Set) * ('a -> 'a) * ('a Set)
