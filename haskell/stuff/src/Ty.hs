{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
module Ty where

import qualified Prelude 

import Data.Kind (Type)

data Nat :: Type where
  O :: Nat
  S :: Nat -> Nat

infixr 6 :>
data Vec :: Type -> Nat -> Type where
  Nil  :: Vec a O
  (:>) :: a -> Vec a m -> Vec a (S m)

zip :: Vec a n -> Vec b n -> Vec (a, b) n
zip Nil Nil = Nil
zip (x :> xs) (y :> ys) = (x, y) :> zip xs ys
