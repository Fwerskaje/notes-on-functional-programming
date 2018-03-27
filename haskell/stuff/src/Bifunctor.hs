{-# LANGUAGE NoImplicitPrelude #-}

module Bifunctor where

import Pre
import Data.Function ((.), id, ($))
import Prelude (Int, (+))

class Bifunctor p where

  bimap :: (a -> b) -> (c -> d) -> p a c -> p b d
  bimap f g = first f . second g

  first :: (a -> b) -> p a c -> p b c
  first f = bimap f id

  second :: (c -> d) -> p a c -> p a d
  second f = bimap id f

instance Bifunctor Either where
  bimap f _ (Left a) = Left (f a)
  bimap _ g (Right b) = Right (g b)

instance Bifunctor (,) where
  bimap f g (x, y) = (f x, g y)
