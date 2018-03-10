{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

module TypeLevel where

data Nat = Zero | Succ Nat

instance Show Nat where
  show n = (++ "N") $ show (natLen n)
           where natLen Zero = 0
                 natLen (Succ k) = 1 + natLen k

data Vector (n :: Nat) (a :: *) where
  VNil :: Vector 'Zero a
  VCons :: a -> Vector n a -> Vector ('Succ n) a

instance Show a => Show (Vector n a) where
  show VNil = "VNil"
  show (VCons a as) = show a ++ " :V: " ++ show as 

type family Add n m where
  Add 'Zero m = m
  Add ('Succ n) m = 'Succ (Add n m)

append :: Vector n a -> Vector m a -> Vector (Add n m) a
append VNil ys = ys
append (VCons x xs) ys = VCons x $ append xs ys

{-

append (VCons 1 (VCons 3 VNil)) (VCons 2 VNil)
1 : 3 : 2 : VNil

-}

data HList xs where
  HNil :: HList '[]
  (:::) :: a -> HList as -> HList (a ': as)
                                  
infixr 6 :::

{-
instance Show (HList xs) where
   show HNil = "HNil"
   show (x ::: xs) = "_ ::: " ++ show xs
-}

instance Show (HList '[]) where
    show HNil = "HNil"

instance (Show (HList as), Show a) => Show (HList (a ': as)) where
    show (x ::: xs) = show x ++ " ::: " ++ show xs

newtype s >> a = Named a

data HRec xs where
    HEmpty :: HRec '[]
    HCons :: (s >> a) -> HRec xs -> HRec (s >> a ': xs)

ex :: HRec '["foo" >> Char, "bar" >> Int]
ex = HCons (Named @"foo" 'a') (HCons (Named @"bar" (3 :: Int)) HEmpty)

instance Show (HRec '[]) where
    show _ = "HEmpty"
