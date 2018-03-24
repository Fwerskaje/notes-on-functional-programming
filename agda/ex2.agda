module ex2 where

data _≡_ {ℓ} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

data 𝔹 : Set where
     tt : 𝔹
     ff : 𝔹

{-# BUILTIN BOOL  𝔹  #-}
{-# BUILTIN TRUE  tt  #-}
{-# BUILTIN FALSE ff #-}

if_then_else_ : ∀ {ℓ} {A : Set ℓ} → 𝔹 → A → A → A
if tt then y else z = y
if ff then y else z = z

_∧_ : 𝔹 → 𝔹 → 𝔹
tt ∧ b = b
ff ∧ tt = ff
ff ∧ ff = ff

_∨_ : 𝔹 → 𝔹 → 𝔹
tt ∨ b = tt
ff ∨ b = b

~_ : 𝔹 → 𝔹
~ tt = ff
~ ff = tt

~tt : (~ (~ tt)) ≡ tt
~tt = refl

~~-elim : ∀ (b : 𝔹) → (~ (~ b)) ≡ b
~~-elim tt = refl
~~-elim ff = refl

∧-same : ∀ {b} → (b ∧ b) ≡ b
∧-same {tt} = refl
∧-same {ff} = refl

test-&&-same : (tt ∧ tt) ≡ tt
test-&&-same = ∧-same

∨-same : ∀ {b} → (b ∨ b) ≡ b
∨-same {tt} = refl
∨-same {ff} = refl

∨≡ff₁ : ∀ {b1 b2} → (b1 ∨ b2) ≡ ff → b1 ≡ ff
∨≡ff₁ {ff} {ff} refl = refl
∨≡ff₁ {tt} {tt} ()
∨≡ff₁ {tt} {ff} ()
∨≡ff₁ {ff} {tt} ()

||-cong₁ : ∀ {b1 b1′ b2} → b1 ≡ b1′ → (b1 ∨ b2) ≡ (b1′ ∨ b2) 
||-cong₁ refl = refl

||-cong₂ : ∀ {b1 b2 b2′} → b2 ≡ b2′ → (b1 ∨ b2) ≡ (b1 ∨ b2′)
||-cong₂ p rewrite p = refl

ite-same : ∀ {a} {A : Set a} → ∀ (b : 𝔹) (x : A) → (if b then x else x) ≡ x
ite-same tt x = refl
ite-same ff x = refl

𝔹-contra : ff ≡ tt → ∀ {P : Set} → P
𝔹-contra ()

-- Ex
-- 1

∧-combo : {p1 p2 : 𝔹} → (p1 ≡ tt) → (p2 ≡ tt) → (p1 ∧ p2) ≡ tt
∧-combo refl refl = refl

-- Ex
-- 2
p : {a b c : 𝔹} → ((~ a) ∨ (~ (b ∨ c))) ≡ ((~ a) ∨ ((~ b) ∧ (~ c)))
p {tt} {tt} {tt} = refl
p {tt} {tt} {ff} = refl
p {tt} {ff} {tt} = refl
p {tt} {ff} {ff} = refl
p {ff} {tt} {tt} = refl
p {ff} {tt} {ff} = refl
p {ff} {ff} {tt} = refl
p {ff} {ff} {ff} = refl

--------

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero + y = y
suc x + y = suc (x + y)

0+ : ∀ (x : ℕ) → (0 + x) ≡ x
0+ x = refl

+0 : ∀ (x : ℕ) → (x + 0) ≡ x
+0 zero = refl
+0 (suc x) rewrite +0 x = refl

+assoc : ∀ (x y z : ℕ) → (x + (y + z)) ≡ ((x + y) + z)
+assoc zero y z = refl
+assoc (suc x) y z rewrite +assoc x y z = refl

+suc : ∀ (x y : ℕ) → (x + suc y) ≡ suc (x + y)
+suc zero y = refl
+suc (suc x) y rewrite +suc x y = refl

+comm : ∀ (x y : ℕ) → (x + y) ≡ (y + x)
+comm zero y rewrite +0 y = refl
+comm (suc x) y rewrite +suc y x | +comm x y = refl

_×_ : ℕ → ℕ → ℕ
zero × y = 0
suc x × y = y + (x × y)

×distribr : ∀ (x y z : ℕ) → ((x + y) × z) ≡ ((x × z) + (y × z))
×distribr zero y z = refl
×distribr (suc x) y z rewrite ×distribr x y z = +assoc z (x × z) (y × z)

×0 : ∀ (x : ℕ) → (x × zero) ≡ zero
×0 zero = refl
×0 (suc x) rewrite ×0 x = refl

×1 : ∀ (x : ℕ) → (x × 1) ≡ x
×1 zero = refl
×1 (suc x) rewrite ×1 x = refl

×suc : ∀ (x y : ℕ) → (x × (suc y)) ≡ (x + (x × y))
×suc zero y = refl
×suc (suc x) y rewrite ×suc x y | +assoc y x (x × y) | +assoc x y (x × y) | +comm y x = refl

×comm : ∀ (x y : ℕ) → (x × y) ≡ (y × x)
×comm zero y rewrite ×0 y = refl
×comm (suc x) y rewrite ×suc y x | ×comm x y = refl

×assoc : ∀ (x y z : ℕ) → (x × (y × z)) ≡ ((x × y) × z)
×assoc zero y z = refl
×assoc (suc x) y z rewrite ×assoc x y z | ×distribr y (x × y) z = refl

_<_ : ℕ → ℕ → 𝔹
zero < zero = ff
zero < suc y = tt
suc x < zero = ff
suc x < suc y = x < y

<-0 : ∀ (x : ℕ) → (x < 0) ≡ ff
<-0 zero = refl
<-0 (suc x) = refl

id : {A : Set} → A → A
id x = x
