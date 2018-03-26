{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE GADTs #-}

module Nat where

import Prelude (Show, Int, Num, (+), ($), show)

data Nat where
  Zero :: Nat
  Suc  :: Nat -> Nat

instance Show Nat where
  show n = show $ go n 0
    where go Zero acc = acc
          go (Suc n) acc = go n (acc + 1)

add :: Nat -> Nat -> Nat
add Zero n = n
add (Suc x) n = Suc (x `add` n) 
