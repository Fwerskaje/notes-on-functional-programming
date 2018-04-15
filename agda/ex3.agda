module ex3 where

open import ex2
open import level using (_⊔_)

_∘_ : {A : Set} {B : A → Set} {C : (x : A) → B x → Set}
      (f : {x : A}(y : B x) → C x y)
      (g : (x : A) → B x)
      (x : A) → C x (g x)
(f ∘ g) x = f (g x)

data _×ₚ_ (α β : Set) : Set where
  <_,_> : α → β → α ×ₚ β

fst : {α β : Set} → (α ×ₚ β) → α
fst < x , x₁ > = x

snd : {α β : Set} → (α ×ₚ β) → β
snd < x , x₁ > = x₁

t₁ : ℕ ×ₚ ℕ
t₁ = < zero , zero >

{-
comp : ∀ {ℓ} {α : Set ℓ} → (n : ℕ) → (f : α → α) → (α → α)
comp = {!!}
  where go : ∀ {ℓ } {α : Set ℓ} → (i : ℕ) → (f : α → α) → (α → α)
        go zero f = f
        go (suc i) f = f ∘ (go i f) -}

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

data Σ {ℓ ℓ′} (α : Set ℓ) (β : α → Set ℓ′) : Set (ℓ ⊔ ℓ′) where
  _,_ : (a : α) → (b : β a) → Σ α β

ℕ⁺ : Set
ℕ⁺ = Σ ℕ (λ n → (iszero n) ≡ ff)

n⁺ : ℕ⁺
n⁺ = 1 , refl

_+⁺_ : ℕ⁺ → ℕ⁺ → ℕ⁺
(zero , ()) +⁺ _
_ +⁺ (zero , ())
(á@(suc _) , b) +⁺ (á₁@(suc _) , b₁) = (á + á₁) , refl

n⁺₁ : ℕ⁺
n⁺₁ = (5 , refl) +⁺ (3 , refl)

fib : ℕ → ℕ
fib n = fib′ n 0 1
  where fib′ : ℕ → ℕ → ℕ → ℕ
        fib′ 0 a _ = a
        fib′ (suc n) a b = fib′ n b (a + b)

data Stream {ℓ} (α : Set ℓ) : Set ℓ where
  σ : (x : α) → (succ : α → α) → Stream α

s₁ : Stream ℕ 
s₁ = σ zero suc

mapStream : {α β : Set} → (f : α → β) → Stream α → Stream β
mapStream f (σ x succ) = ?

take : ∀ {ℓ} {α : Set ℓ} → (i : ℕ) → Stream α → 𝕍 α i
take zero _ = []
take (suc i) (σ x succ) = (x ∷ (take i (σ (succ x) succ)))

ℕ-fib-σ : Stream (ℕ ×ₚ ℕ)
ℕ-fib-σ = σ < zero , zero > next₁
  where next₁ : (ℕ ×ₚ ℕ) → (ℕ ×ₚ ℕ)
        next₁ < x , x₁ > = < suc x , fib (suc x) >

fibs′ : 𝕃 ℕ
fibs′ = map fib (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])

fibs : (i : ℕ) → 𝕍 ℕ i
fibs zero = []
fibs í@(suc i) = map𝕍 snd (take í ℕ-fib-σ)

{-
ℕ-fib : Set
ℕ-fib = Σ ℕ (λ n → ( -}

