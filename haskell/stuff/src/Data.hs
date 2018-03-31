{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE GADTs #-}

module Data where

import Prelude (Show, show, ($), (++))

data A = A deriving Show
data B = B deriving Show
data C = C deriving Show

ab :: A -> B
ab A = B

ba :: B -> A
ba B = A

bc :: B -> C
bc B = C

data Maybe a =
    Just a
  | Nothing
  deriving Show

data Either a b =
    Left a
  | Right b
  deriving Show

data Pair a = Pair a a
  deriving Show

data List a where
  Nil :: List a
  Cons :: a -> List a -> List a

data Free f a =
    Var a
  | Node (f (Free f a))

(+++) :: List a -> List a -> List a
Nil +++ ys = ys
(Cons x xs) +++ ys = Cons x (xs +++ ys)

zipWith :: (a -> b -> c) -> List a -> List b -> List c
zipWith _ Nil _ = Nil
zipWith _ _ Nil = Nil 
zipWith f (Cons x xs) (Cons y ys) = Cons (f x y) $ zipWith f xs ys

instance Show a => Show (List a) where
  show Nil = "[]"
  show (Cons x xs) = (show x) ++ " : " ++ show xs
