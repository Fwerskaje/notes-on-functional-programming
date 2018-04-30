{-# LANGUAGE UnicodeSyntax #-}
module Pointfree where

takeWhile' :: (a → Bool) → [a] → [a]
takeWhile' = (fst .) . span

{-

((f .) .) . g ≡ f (g x y z)

-}

ex1 :: Integer → Integer → Integer
ex1 = (succ .) . (+)

ex2 :: Integer
ex2 = (((product .) .) . zipWith) (+) [1,2,3] [3,2,1]

{-

(g . f) ≡ (. f) g ⇒ (g . f)

-}

newtype Predicate a =
  Predicate { getPredicate :: a → Bool }

class Contravariant f where
  contramap :: (a → b) → f b → f a

newtype Op z a = Op {getOp :: a → z}

instance Contravariant (Op z) where
  contramap h (Op g) = Op $ g . h

instance Contravariant Predicate where
  contramap f (Predicate g) = Predicate $ g . f

lengther :: Op Int [a]
lengther = Op length

nLengther :: Op Int Int
nLengther = contramap (\x → [1..x]) lengther

veven :: Predicate Integer
veven = contramap (`div` 2) $ Predicate even

