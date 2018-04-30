module Sigma where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc; fromℕ)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n; _+_; _*_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Function using (_$_; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Empty using (⊥)
open import Data.Vec using (Vec; _∷_; [])
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Coinduction using (∞; ♯_; ♭)


data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (a : A) → (b : B a) → Σ A B

infixr 4 _,_

n₁ : Σ (List ℕ) (λ z → length z ≡ 5)
n₁ = 1 ∷ 2 ∷ 2 ∷ 3 ∷ 4 ∷ [] , refl 

n₂ : Σ ℕ (λ m → m < 5)
n₂ = 4 , s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))

n₃ : Σ ℕ (λ k → k + 3 ≡ 5)
n₃ = 2 , refl

data Stream (A : Set) : Set where
  _∷_ : A → ∞ (Stream A) → Stream A

infixr 5 _∷_

data ℕω : Set where
  zero : ℕω
  suc : ∞ ℕω → ℕω

n₄ : ℕω
n₄ = suc (♯ suc (♯ suc (♯ suc (♯ zero))))

data ℕ⁻ : Set where
  suc  : ℕ⁻ → ℕ⁻

--n₅ : ℕ⁻
--n₅ = suc n₅ -- termination checking error.

data Ω : Set where
  suc  : ∞ Ω → Ω

n₆ : Ω
n₆ = suc (♯ n₆)

ω : ℕω
ω = suc (♯ ω)

streamℕ : (n : ℕ) → Stream ℕ
streamℕ n = n ∷ ♯(streamℕ (suc n))

n₇ : Stream ℕ
n₇ = streamℕ 0

head : {A : Set} → Stream A → A
head (x ∷ xs) = x

tail : {A : Set} → Stream A → Stream A
tail (x ∷ xs) = ♭ xs

lookup : {A : Set} → ℕ → Stream A → A
lookup zero    (x ∷ xs) = x
lookup (suc n) (x ∷ xs) = lookup n (♭ xs)

take : {A : Set} (n : ℕ) → Stream A → Vec A n
take zero    xs       = []
take (suc n) (x ∷ xs) = x ∷ take n (♭ xs)

drop : {A : Set} → ℕ → Stream A → Stream A
drop zero    xs       = xs
drop (suc n) (x ∷ xs) = drop n (♭ xs)

data Colist (A : Set) : Set where
  []  : Colist A
  _∷_ : A → ∞ (Colist A) → Colist A

n₈ : Colist ℕ
n₈ = 0 ∷ ♯ (1 ∷ ♯ [])

toColist : {A : Set} → Stream A → Colist A
toColist (x ∷ xs) = x ∷ ♯ toColist (♭ xs)

infix 4 _≈_
data _≈_ {A : Set} : Stream A → Stream A → Set where
  _∷_ : (x : A) {xs ys : ∞ (Stream A)} → ∞ (♭ xs ≈ ♭ ys) → x ∷ xs ≈ x ∷ ys

≈-refl : {A : Set} {xs : Stream A} → xs ≈ xs
≈-refl {A} {x ∷ xs} = x ∷ ♯ ≈-refl




