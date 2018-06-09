module ex3 where

open import ex2
open import Level hiding (zero; suc) -- using (_⊔_) lone

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

the : (α : Set) → α → α
the α = id

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

{-
mapStream : {α β : Set} → (f : α → β) → Stream α → Stream β
mapStream f (σ x succ) = {!!}
-}

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

data ⊤ : Set where
  triv : ⊤

ℤ-pos-t : ℕ → Set
ℤ-pos-t zero = ⊤
ℤ-pos-t (suc _) = 𝔹

data ℤ : Set where
  Mkℤ : (n : ℕ) → ℤ-pos-t n → ℤ

0ℤ : ℤ
0ℤ = Mkℤ zero triv

1ℤ : ℤ
1ℤ = Mkℤ 1 tt

-1ℤ : ℤ
-1ℤ = Mkℤ 1 ff

z-pos : ∀ (x y : ℕ) (a : (x > y)  ≡ tt) (b : 𝔹) → ℤ-pos-t (x - y 「 x>y⇒x≥y x y a 」)
z-pos zero zero () _
z-pos zero (suc y) () _
z-pos (suc x) zero refl b = b 
z-pos (suc x) (suc y) a b = z-pos x y a b

rev-> : ∀ (x y : ℕ) → (y < x) ≡ tt → (x > y) ≡ tt
rev-> zero zero ()
rev-> zero (suc _) ()
rev-> (suc x) zero refl = refl
rev-> (suc x) (suc y) p rewrite rev-> x y p = refl

_+ℤ_ : ℤ → ℤ → ℤ
Mkℤ zero _        +ℤ y            = y
Mkℤ n@(suc _)  x  +ℤ Mkℤ zero _   = Mkℤ n x
Mkℤ n@(suc _)  x  +ℤ Mkℤ n₂@(suc _)   x₁ with < compareℕ n n₂ , x ⊻ x₁ >
Mkℤ n@(suc _)  x  +ℤ Mkℤ n₂@(suc _)   _  | < _ , ff > = Mkℤ (n + n₂) x
Mkℤ n@(suc n′) x  +ℤ Mkℤ n₂@(suc n′₂) x₁ | < Left   a , tt > = Mkℤ n″ (z-pos n′ n′₂ a x)
  where n″ = n - n₂ 「 x>y⇒x≥y n′ n′₂ a 」
Mkℤ n@(suc n′) x  +ℤ Mkℤ n₂@(suc n′₂) x₁ | < Right  c , tt > = Mkℤ n″ (z-pos n′₂ n′ (rev-> n′₂ n′ c) x₁)
  where n″ = n₂ - n 「 x>y⇒x≥y n′₂ n′ (rev-> n′₂ n′ c) 」
Mkℤ n@(suc n′) x  +ℤ Mkℤ n₂@(suc n′₂) x₁ | < Middle b , tt > = Mkℤ zero triv

x₁ : ℤ
x₁ = (Mkℤ 42 tt) +ℤ (Mkℤ 265 ff) 

_≤ℤ_ : ℤ → ℤ → 𝔹
Mkℤ zero triv ≤ℤ Mkℤ zero triv = tt
Mkℤ zero triv ≤ℤ Mkℤ (suc m) y = y   -- +N > 0 ⇒ tt; -N > 0 ⇒ ff
Mkℤ (suc n) x ≤ℤ Mkℤ zero triv = ~ x -- +N < 0 ⇒ ff; -N < 0 ⇒ tt
Mkℤ (suc n) tt ≤ℤ Mkℤ (suc m) tt = n ≤ m
Mkℤ (suc n) ff ≤ℤ Mkℤ (suc m) ff = n ≥ m
Mkℤ (suc _) tt ≤ℤ Mkℤ (suc _) ff = ff
Mkℤ (suc _) ff ≤ℤ Mkℤ (suc _) tt = tt


_≥ℤ_ : ℤ → ℤ → 𝔹
_≥ℤ_ x y = y ≤ℤ x -- x ≥ y ⇒ y ≤ x

_≠ℤ_ : ℤ → ℤ → 𝔹
Mkℤ zero triv ≠ℤ Mkℤ zero triv = tt
Mkℤ zero triv ≠ℤ Mkℤ (suc _) _ = ff
Mkℤ (suc _) _ ≠ℤ Mkℤ zero triv = ff
Mkℤ (suc n) x ≠ℤ Mkℤ (suc m) y = (~ (x ⊻ y)) ∧ (n ≠ℕ m)

_<ℤ_ : ℤ → ℤ → 𝔹
_<ℤ_ x y = (x ≤ℤ y) ∧ (x ≠ℤ y)

_>ℤ_ : ℤ → ℤ → 𝔹
_>ℤ_ x y = y <ℤ x

{-
Define some further operations on the type Z of Section 7.1,
such as negation, subtraction, and multiplication.
-}

-_ : ℤ → ℤ 
- Mkℤ zero triv = Mkℤ zero triv
- Mkℤ n@(suc _) x = Mkℤ n (~ x)

{-
a-plus-minus-a-≡0 : ∀ (a : ℤ) → (a +ℤ (- a)) ≡ (Mkℤ zero triv)
a-plus-minus-a-≡0 (Mkℤ zero triv) = refl
a-plus-minus-a-≡0 (Mkℤ (suc n) x) = {!!}
  where prf : ∀ (n x : ℕ) →
              (Mkℤ (suc n) x +ℤ Mkℤ (suc n) (~ x) | < compareℕ n n , x ⊻ (~ x) >)
              ≡ Mkℤ 0 triv
        prf = ?-}
  

_×ℤ_ : ℤ → ℤ → ℤ
Mkℤ zero triv ×ℤ Mkℤ zero triv = Mkℤ zero triv
Mkℤ zero triv ×ℤ Mkℤ (suc _) _ = Mkℤ zero triv
Mkℤ (suc _) _ ×ℤ Mkℤ zero triv = Mkℤ zero triv
n@(Mkℤ (suc _) x) ×ℤ Mkℤ (suc zero) x₂ = {!!} -- Mkℤ ? ((~ (x ⊻ x₂)) ∧ (x ∧
n@(Mkℤ (suc _) _) ×ℤ Mkℤ (suc (suc n₂)) x₂ = {!!}

