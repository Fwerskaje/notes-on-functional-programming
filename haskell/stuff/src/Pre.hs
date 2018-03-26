{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE GADTs #-}

module Pre where

import Prelude (Show, Int, Num, (+), (++), ($), show)

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
