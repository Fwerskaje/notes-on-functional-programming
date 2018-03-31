{-# LANGUAGE NoImplicitPrelude #-}

module Monad where

import Pre
import Applicative
import Functor

class Applicative m => Monad m where
  (>>=) :: m a -> (a -> m b) -> m b
  (=<<) :: (a -> m b) -> m a -> m b
  (=<<) = flip (>>=)

class Applicative m => Monad' m where
  join :: m (m a) -> m a
  
  bindR :: (a -> m b) -> m a -> m b
  bindR f = join . (map f)
  
  bind :: m a -> (a -> m b) -> m b
  bind = flip bindR

(>=>) :: Monad m => (a -> m b) -> (b -> m c) -> a -> m c
g >=> h = ((=<<) h) . g

instance Monad Maybe where
  Nothing  >>= _ = Nothing
  (Just a) >>= g = g a

instance Monad' Maybe where
  join Nothing = Nothing
  join (Just (Just n)) = Just n
