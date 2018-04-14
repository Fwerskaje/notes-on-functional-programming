{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
module Fam where

class Add a b where
  type SumTy a b :: *
  plus :: a -> b -> SumTy a b

instance Add Integer Double where
  type SumTy Integer Double = Double
  plus x y = fromIntegral x + y

instance Add Double Integer where
  type SumTy Double Integer = Double
  plus x y = x + fromIntegral y

instance (Num a) => Add a a where
  type SumTy a a = a
  plus x y = x + y

ex1 :: IO ()
ex1 = print $ plus (5 :: Integer) (6 :: Double)

data L
data V val
data C a b

data F f where
  Lit :: String -> F L
  Val :: Show a => F (V a)
  Comp :: F f1 -> F f2 -> F (C f1 f2)

lit :: String -> F L
lit str = Lit str

int :: F (V Int)
int = Val

string :: F (V String)
string = Val

infixl 5 <>
(<>) = Comp

