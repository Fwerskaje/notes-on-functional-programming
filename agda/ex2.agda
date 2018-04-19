{-# OPTIONS --allow-unsolved-metas #-}

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

_=𝔹_ : 𝔹 → 𝔹 → 𝔹
tt =𝔹 tt = tt
tt =𝔹 ff = ff
ff =𝔹 tt = ff
ff =𝔹 ff = tt

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

_⊻_ : 𝔹 → 𝔹 → 𝔹
tt ⊻ tt = tt
ff ⊻ ff = tt
tt ⊻ ff = ff
ff ⊻ tt = ff

~_ : 𝔹 → 𝔹
~ tt = ff
~ ff = tt

~tt : (~ (~ tt)) ≡ tt
~tt = refl

∧-commutative : ∀ (b c : 𝔹) -> (b ∧ c) ≡ (c ∧ b)
∧-commutative tt tt = refl
∧-commutative tt ff = refl
∧-commutative ff tt = refl
∧-commutative ff ff = refl

∧-true-elim : ∀ (b c : 𝔹) → (b ∧ c) ≡ tt → c ≡ tt
∧-true-elim tt c p = p -- Hm~
∧-true-elim ff tt p = refl
∧-true-elim ff ff ()

∧-eq-∨ : ∀ (b c : 𝔹) -> (b ∧ c) ≡ (b ∨ c) → b ≡ c
∧-eq-∨ tt tt refl = refl
∧-eq-∨ ff tt ()
∧-eq-∨ ff ff refl = refl

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

pred : ℕ → ℕ
pred zero = zero
pred (suc n) = n

0+ : ∀ (x : ℕ) → (0 + x) ≡ x
0+ x = refl

+0 : ∀ (x : ℕ) → (x + 0) ≡ x
+0 zero = refl
+0 (suc x) rewrite +0 x = refl

+suc : ∀ (x y : ℕ) → (x + suc y) ≡ suc (x + y)
+suc zero y = refl
+suc (suc x) y rewrite +suc x y = refl

+comm : ∀ (x y : ℕ) → (x + y) ≡ (y + x)
+comm zero y rewrite +0 y = refl
+comm (suc x) y rewrite +suc y x | +comm x y = refl

_×_ : ℕ → ℕ → ℕ
zero × y = 0
suc x × y = y + (x × y)

iszero : (n : ℕ) → 𝔹
iszero zero = tt
iszero (suc _) = ff

+assoc : ∀ (x y z : ℕ) → (x + (y + z)) ≡ ((x + y) + z)
+assoc zero y z = refl
+assoc (suc x) y z rewrite +assoc x y z = refl

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

_^_ : ℕ → ℕ → ℕ
zero  ^ _    = 0
suc _ ^ zero = 1
x′@(suc x) ^ suc y = x′ × (x′ ^ y)

x¹ : ℕ
x¹ = 3 ^ 5 -- 243

data Either : (α β : Set) → Set where
  Left  : {α β : Set} → (a : α) → Either α β
  Right : {α β : Set} → (b : β) → Either α β

data Either³ : (α β γ : Set) → Set where
  Left   : {α β γ : Set} → (a : α) → Either³ α β γ
  Middle : {α β γ : Set} → (b : β) → Either³ α β γ
  Right  : {α β γ : Set} → (c : γ) → Either³ α β γ

_<_ : ℕ → ℕ → 𝔹
zero < zero = ff
zero < suc y = tt
suc x < zero = ff
suc x < suc y = x < y

<-0 : ∀ (x : ℕ) → (x < 0) ≡ ff
<-0 zero = refl
<-0 (suc x) = refl

_=ℕ_ : ℕ → ℕ → 𝔹
zero  =ℕ zero  = tt
zero  =ℕ suc _ = ff
suc _ =ℕ zero  = ff
suc x =ℕ suc y = x =ℕ y

_≠ℕ_ : ℕ → ℕ → 𝔹
x ≠ℕ y = ~ (x =ℕ y)

_>_ : ℕ → ℕ → 𝔹
x > y = (~ (x < y)) ∧ (x ≠ℕ y)

<⇒> : ∀ (x y : ℕ) → (x > y) ≡ (y < x)
<⇒> zero zero = refl
<⇒> zero (suc y) = refl
<⇒> (suc x) zero = refl
<⇒> (suc x) (suc y) = <⇒> x y

_≤_ : ℕ → ℕ → 𝔹
x ≤ y = (x < y) ∨ (x =ℕ y)

_≥_ : ℕ → ℕ → 𝔹
x ≥ y = (x > y) ∨ (x =ℕ y)

zeroXzeroY : ∀ (x y : ℕ) → (x =ℕ 0) ≡ tt → (x =ℕ y) ≡ tt → (y =ℕ 0) ≡ tt
zeroXzeroY zero    zero    prf₁ prf₂ = refl
zeroXzeroY zero    (suc _) refl ()
zeroXzeroY (suc x) zero    ()   _
zeroXzeroY (suc x) (suc y) ()   _

ℕComp : (x : ℕ) → (y : ℕ) → Set
ℕComp x y = Either³ ((x > y) ≡ tt) ((x =ℕ y) ≡ tt) ((x < y) ≡ tt)

compareℕ : (x : ℕ) → (y : ℕ) → ℕComp x y
compareℕ zero zero = Middle refl
compareℕ zero (suc _) = Right refl
compareℕ (suc _) zero = Left refl
compareℕ (suc x) (suc y) = compareℕ x y 

prf≤¹ : ∀ (x y : ℕ) → (suc x ≤ suc y) ≡ tt → (x ≤ suc y) ≡ tt
prf≤¹ zero zero refl = refl
prf≤¹ zero (suc y) refl = refl
prf≤¹ (suc x) zero ()
prf≤¹ (suc x) (suc y) p rewrite prf≤¹ x y p = refl

_-_「_」 : (x : ℕ) → (y : ℕ) → (x ≥ y) ≡ tt → ℕ
zero       - zero  「 refl 」 = zero
zero       - suc _ 「 () 」
x@(suc _)  - zero  「 refl 」 = x
suc x      - suc y 「 p 」 = x - y 「 p 」

x₃ : (43 - 17 「 refl 」) ≡ 26
x₃ = refl

minus : ℕ → ℕ → ℕ
minus zero y = 0
minus x@(suc _) zero = x
minus (suc x) (suc y) = minus x y 

{-
division :: Int -> Int -> Int
division = go 0
  where go acc n d
          | n >= d = go (acc + 1) (n - d) d
          | otherwise = acc
-}

≥⇒≤ : ∀ (x y : ℕ) → (x ≥ y) ≡ tt → (y ≤ x) ≡ tt
≥⇒≤ zero zero refl = refl
≥⇒≤ zero (suc _) ()
≥⇒≤ (suc x) zero refl = refl
≥⇒≤ (suc x) (suc y) p rewrite ≥⇒≤ x y p = refl

∀ℕ⇒ℕ≥0 : ∀ (n : ℕ) → (n ≥ 0) ≡ tt
∀ℕ⇒ℕ≥0 zero    = refl
∀ℕ⇒ℕ≥0 (suc _) = refl 

x-eq-x : ∀ (x : ℕ) → (x =ℕ x) ≡ tt
x-eq-x zero    = refl
x-eq-x (suc x) = x-eq-x x

xMinusZero : ∀ (x : ℕ) → ((x - 0 「 ∀ℕ⇒ℕ≥0 x 」) =ℕ x) ≡ tt
xMinusZero zero    = refl
xMinusZero (suc x) = x-eq-x x

minusXprf : ∀ (x y : ℕ) →
              (prf : (x ≥ y) ≡ tt) →
              ((x ≠ℕ 0) ∧ (y ≠ℕ 0)) ≡ tt →
              (x > (x - y 「 prf 」)) ≡ tt
minusXprf zero zero refl ()
minusXprf zero (suc y) () ()
minusXprf (suc x) zero refl ()
minusXprf (suc x) (suc y) p1 p2 = {!!}

minusXYprf : ∀ (d n : ℕ) → (d > n) ≡ tt → (d > minus n d) ≡ tt
minusXYprf zero zero ()
minusXYprf zero (suc _) ()
minusXYprf (suc _) zero refl = refl
minusXYprf (suc d) (suc n) prf {- rewrite minusXYprf d n prf -} = {!!}

x>y⇒x≥y : ∀ (x y : ℕ) → (x > y) ≡ tt → (x ≥ y) ≡ tt
x>y⇒x≥y zero zero ()
x>y⇒x≥y zero (suc y) ()
x>y⇒x≥y (suc x) zero refl = refl
x>y⇒x≥y (suc x) (suc y) p = x>y⇒x≥y x y p

dn-eq-dn-beq : ∀ (d n : ℕ) → (d =ℕ n) ≡ tt → (d ≥ n) ≡ tt
dn-eq-dn-beq zero zero refl = refl
dn-eq-dn-beq zero (suc n) ()
dn-eq-dn-beq (suc d) zero ()
dn-eq-dn-beq (suc d) (suc n) p = dn-eq-dn-beq d n p

ℕComp² : (x y : ℕ) → Set
ℕComp² x y = Either ((x ≥ y) ≡ tt) ((x ≤ y) ≡ tt)

compareℕ₂ : (x y : ℕ) → ℕComp² x y
compareℕ₂ zero zero = Left refl
compareℕ₂ zero (suc y) = Right refl
compareℕ₂ (suc x) zero = Left refl
compareℕ₂ (suc x) (suc y) = compareℕ₂ x y

division : (x : ℕ) → (y : ℕ) → (y ≠ℕ 0) ≡ tt → ℕ
division _ zero ()
division zero (suc _) _ = 0
division n′@(suc x) d′@(suc y) refl = go n′ d′ 0 n′ (compareℕ₂ x y) refl refl -- d ≤ n
  where go : (n : ℕ) → (d : ℕ) → (acc : ℕ) → (count : ℕ) → ℕComp² n d → (count ≠ℕ 0) ≡ tt → (d ≠ℕ 0) ≡ tt → ℕ
        go n zero acc count p1 p2 ()
        go n (suc d) acc zero p1 () p3
        go zero (suc d) acc (suc count) (Left ()) p2 p3
        go zero (suc d) acc (suc count) (Right b) p2 p3 = acc
        go (suc n) (suc d) acc (suc count) (Right b) p2 p3 = acc
        go (suc n) d″@(suc d) acc (suc count) (Left a) p2 p3 =
          go n″ d″ (suc acc) count (compareℕ₂ n″ d″) {!!} refl
             where n″ = (n - d 「 a 」)

n₁ : ((division 42 2 refl) =ℕ 21) ≡ tt
n₁ = {!!} -- refl 

≤-trans : ∀ {x y z : ℕ} → (x ≤ y) ≡ tt → (y ≤ z) ≡ tt → (x ≤ z) ≡ tt
≤-trans {zero}  {zero}  {z}     refl prf₂ = prf₂
≤-trans {zero}  {suc y} {zero}  refl _    = refl
≤-trans {zero}  {suc y} {suc z} refl _    = refl
≤-trans {suc x} {zero}  {zero}  () 
≤-trans {suc x} {zero}  {suc z} () 
≤-trans {suc x} {suc y} {zero}  _    prf₂ = prf₂
≤-trans {suc x} {suc y} {suc z} prf₁ prf₂ rewrite ≤-trans {x} {y} {z} prf₁ prf₂ = refl

≤-suc : ∀ (x : ℕ) → (x ≤ (suc x)) ≡ tt
≤-suc zero = refl
≤-suc (suc x) = ≤-suc x

id : {A : Set} → A → A
id x = x

infixr 40 _∷_

data 𝕃 {ℓ} (A : Set ℓ) : Set ℓ where
  [] : 𝕃 A
  _∷_ : (x : A) (xs : 𝕃 A) → 𝕃 A

xs₁ : 𝕃 ℕ
xs₁ = 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []

length : ∀ {ℓ} {A : Set ℓ} → 𝕃 A → ℕ
length [] = zero
length (_ ∷ xs) = 1 + length xs

_++_ : ∀ {ℓ} {A : Set ℓ} → 𝕃 A → 𝕃 A → 𝕃 A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

map : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} → (A → B) → 𝕃 A → 𝕃 B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

filter : ∀ {ℓ} {A : Set ℓ} → (f : A → 𝔹) → 𝕃 A → 𝕃 A
filter f [] = []
filter f (x ∷ xs) =
  if (f x) then x ∷ (filter f xs)
  else filter f xs

remove : ∀ {ℓ} {A : Set ℓ} (eq : A → A → 𝔹) (a : A) (xs : 𝕃 A) → 𝕃 A
remove eq a = filter (eq a)

data Maybe {ℓ} (A : Set ℓ) : Set ℓ where
  Just : A → Maybe A
  Nothing : Maybe A

nth : ∀ {ℓ} {A : Set ℓ} → ℕ → 𝕃 A → Maybe A
nth n [] = Nothing
nth zero (x ∷ xs) = Just x
nth (suc n) (x ∷ xs) = nth n xs

reverse : ∀ {ℓ} {A : Set ℓ} → 𝕃 A → 𝕃 A
reverse xs = reverse-helper [] xs
  where reverse-helper : ∀ {ℓ} {A : Set ℓ} → 𝕃 A → 𝕃 A → 𝕃 A
        reverse-helper h [] = h
        reverse-helper h (x ∷ xs) = reverse-helper (x ∷ h) xs

length-++ : ∀ {ℓ} {A : Set ℓ} (l₁ l₂ : 𝕃 A) → (length (l₁ ++ l₂)) ≡ ((length l₁) + (length l₂))
length-++ [] l₂ = refl
length-++ (x ∷ l₁) l₂ rewrite length-++ l₁ l₂ = refl

++-assoc : ∀ {ℓ} {A : Set ℓ} (l₁ l₂ l₃ : 𝕃 A) → ((l₁ ++ l₂) ++ l₃) ≡ (l₁ ++ (l₂ ++ l₃))
++-assoc [] l₂ l₃ = refl
++-assoc (x ∷ l₁) l₂ l₃ rewrite ++-assoc l₁ l₂ l₃ = refl

length-filter : ∀ {ℓ} {A : Set ℓ} (p : A → 𝔹) (l : 𝕃 A) → ((length (filter p l)) ≤ (length l)) ≡ tt
length-filter p [] = refl
length-filter p (x ∷ xs) with p x 
… | tt = length-filter p xs
… | ff =
  ≤-trans {length (filter p xs)} (length-filter p xs) (≤-suc (length xs))

