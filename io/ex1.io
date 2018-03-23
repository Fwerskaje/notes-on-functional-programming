# ADT

# Doesn't work.

Maybe   := Object clone

Nothing := Maybe clone
Just    := Maybe clone
Just value := Nothing

Functor := Object clone
Functor map := Nothing

MaybeFunctor := Functor clone
Maybe asFunctor := MaybeFunctor
MaybeFunctor map = method(f, maybe,
        if(maybe == Nothing,
                Nothing clone,
                (
                   result := Just clone
                   result value = f(maybe value)
                   result
                )
        )
)

safeDiv := method(x, y,
        if(y == 0,
                Nothing clone,
                result := Just clone
                result value = (x / y)
                result
          )
)

val1 := safeDiv(3,4)
val2 := safeDiv(5,0)

F := Object clone
F succ := method(n,
        n + 1
)

id := method(n, n)

fJust := method(f, j, (
        n := Just clone
        n value = f(j value)
        n
       )
)

#res0 := (Maybe asFunctor map)(succ, val1)
#res1 := (Maybe asFunctor map)(succ, val2)
