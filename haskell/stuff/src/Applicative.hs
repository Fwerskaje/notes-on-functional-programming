{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Applicative where

import Functor
import Pre

class Functor f => Applicative f where
  pure :: a -> f a
  infixl 4 <*>
  (<*>) :: f (a -> b) -> f a -> f b

instance Applicative Maybe where
  pure = Just
  (Just f) <*> app = map f app
  Nothing <*> app = Nothing

newtype ZipList a = ZipList { getZipList :: List a }
  deriving (Functor)

instance Applicative ZipList where
  pure x = ZipList $ Cons x Nil
  (ZipList gs) <*> (ZipList xs) = ZipList $ zipWith ($) gs xs

instance Applicative List where
  pure x = Cons x Nil
  Nil <*> _ = Nil
  (Cons g gs) <*> xs = (map g xs) +++ (gs <*> xs)

instance Applicative ((->) e) where
  pure = const
  (<*>) f g x = f x $ g x

liftA :: Applicative f => (a -> b) -> f a -> f b
liftA = map

liftA2 :: Applicative f => (a -> b -> c) -> f a -> f b -> f c
liftA2 g f1 f2 = g <$> f1 <*> f2

(<**>) :: Applicative f => f a -> f (a -> b) -> f b
(<**>) = liftA2 (\a f -> f a)

{-
sequenceAL :: Applicative f => List (f a) -> f (List a)
sequenceAL Nil = Nil
sequenceAL (Cons
-}
