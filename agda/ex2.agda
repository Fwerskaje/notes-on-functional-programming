module ex2 where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

data 𝔹 : Set where
     tt : 𝔹
     ff : 𝔹

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
