module G2 where

import Debug.Trace

f :: t
f = let x = x in x 

example :: Int
example = trace "example was called" 42

facto :: Integer -> Integer
facto n = foldr (\x acc -> (trace ("val: " ++ show x ++ "\n") x)
                           *
                           (trace ("acc: " ++ show acc) acc)) 1 [1..n]

f2 :: IO ()
f2 = putStrLn $ show example
