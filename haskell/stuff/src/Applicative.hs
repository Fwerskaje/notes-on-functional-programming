{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Applicative where

import Functor
import Pre
import Data.Function ((.), ($), id)
import Prelude (Int, (+))

class Functor f => Applicative f where
  pure :: a -> f a
  infixl 4 <*>
  (<*>) :: f (a -> b) -> f a -> f b

instance Applicative Maybe where
  pure x = Just x
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
