{-# LANGUAGE NoImplicitPrelude #-}

module Monad where

import Pre
import Applicative

class Applicative m => Monad m where
  (>>=) :: m a -> (a -> m b) -> m b

instance Monad Maybe where
  Nothing >>= _ = Nothing
  (Just a) >>= g = g a

instance Monad ((->) e) where
  f >>= g = \x -> g (f x) x -- WTF


  
