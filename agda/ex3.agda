module ex3 where

open import ex2

data 𝕍 {ℓ} (α : Set ℓ) : ℕ → Set ℓ where
  [] : 𝕍 α 0
  _∷_ : {n : ℕ} (x : α) (xs : 𝕍 α n) → 𝕍 α (suc n)

test-vector : 𝕍 𝔹 4
test-vector = tt ∷ (tt ∷ (tt ∷ (tt ∷ [])))

_++𝕍_ : ∀ {ℓ} {α : Set ℓ} {n m : ℕ} → 𝕍 α n → 𝕍 α m → 𝕍 α (n + m)
[] ++𝕍 ys = ys
(x ∷ xs) ++𝕍 ys = x ∷ (xs ++𝕍 ys)

test-vector-append : 𝕍 𝔹 8
test-vector-append = test-vector ++𝕍 test-vector

head𝕍 : ∀ {ℓ} {α : Set ℓ} {n : ℕ} → 𝕍 α (suc n) → α
head𝕍 (x ∷ _) = x

tail𝕍 : ∀ {ℓ} {α : Set ℓ} {n : ℕ} → 𝕍 α n → 𝕍 α (pred n)
tail𝕍 [] = []
tail𝕍 (x ∷ xs) = xs

map𝕍 : ∀ {ℓ ℓ′} {α : Set ℓ} {β : Set ℓ′} {n : ℕ} → (α → β) → 𝕍 α n → 𝕍 β n
map𝕍 f [] = []
map𝕍 f (x ∷ xs) = f x ∷ map𝕍 f xs

concat𝕍 : ∀ {ℓ} {α : Set ℓ} {n m : ℕ} → 𝕍 (𝕍 α n) m → 𝕍 α (m × n)
concat𝕍 [] = []
concat𝕍 (xs ∷ xs₂) = xs ++𝕍 (concat𝕍 xs₂)

nth𝕍 : ∀ {ℓ} {α : Set ℓ} {n : ℕ} → (xs : 𝕍 α n) → (i : ℕ) → (i < n) ≡ tt → α
nth𝕍 [] zero ()
nth𝕍 [] (suc _) ()
nth𝕍 (x ∷ _) zero p = x
nth𝕍 (_ ∷ xs) (suc i) p = nth𝕍 xs i p

repeat𝕍 : ∀ {ℓ} {α : Set ℓ} → (a : α) → (n : ℕ) → 𝕍 α n
repeat𝕍 a zero = []
repeat𝕍 a (suc n) = a ∷ repeat𝕍 a n

module braun-tree {ℓ} (α : Set ℓ) (_<α_ : α → α → 𝔹) where
