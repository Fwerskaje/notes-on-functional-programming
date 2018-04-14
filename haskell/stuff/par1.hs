module Par1 where

x :: Integer
x = 1 + 2

{-
:sprint x
x = _

The special symbol _ indicates “unevaluated.”

:sprint x
x = 3
-}

y :: Integer
y = x + 1

z :: (Integer, Integer)
z = (x, x + 1)

{-
:sprint z
z = (_,_)
-}

xs :: [Integer]
xs = map (+1) [1..10]

{-
:sprint xs
xs = _

seq xs ()
()

:sprint xs
xs = _ : _

length xs
10

:sprint xs
xs = [_,_,_,_,_,_,_,_,_,_]

head xs 
2

last xs
11

:sprint xs
xs = [2,_,_,_,_,_,_,_,_,11]
-}
