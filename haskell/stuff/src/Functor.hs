{-# LANGUAGE NoImplicitPrelude #-}

module Functor where

import Pre
import Data.Function (($), (.), const)

class Functor f where 
  map :: (a -> b) -> f a -> f b
  
  (<$>) :: (a -> b) -> f a -> f b
  (<$>) = map
  
  (<$) :: a -> f b -> f a
  (<$) = map . const

instance Functor Maybe where
  map f (Just a) = Just $ f a
  map _ Nothing = Nothing

instance Functor (Either a) where
  map f (Right b) = Right $ f b
  map f (Left a) = Left a
  
instance Functor List where
  map f Nil = Nil
  map f (Cons x xs) = (Cons (f x) (map f xs))

instance Functor ((,) a) where
  map f (x, y) = (x, f y)

instance Functor Pair where
  map f (Pair x y) = Pair (f x) (f y)

instance Functor ((->) e) where
  map g x = g . x
