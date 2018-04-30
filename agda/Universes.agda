module Universes where

open import Data.Nat

data False  : Set where
record True : Set where

data Bool : Set where
  true : Bool
  false : Bool

isTrue : Bool → Set
isTrue true = True
isTrue false = False

infix  30 not_
infixr 25 _and_

not_ : Bool → Bool
not true  = false
not false = true

_and_ : Bool → Bool → Bool
true and x = x
false and _ = false

notNotId : (a : Bool) → isTrue (not not a) → isTrue a
notNotId true p = p
notNotId false ()

andIntro : (a b : Bool) → isTrue a → isTrue b → isTrue (a and b)
andIntro true false _ () 
andIntro false b () _
andIntro true true prf₁ _ = prf₁

nonZero : ℕ → Bool
nonZero zero = false
nonZero (suc _) = true

postulate _div_ : ℕ → (m : ℕ) {p : isTrue (nonZero m)} → ℕ

n : ℕ
n = (4 div 2) + 1


