module Ex1 where

data Bool : Set where
  true : Bool
  false : Bool

data Maybe (A : Set) : Set where
  Nothing : Maybe A
  Just a : (a : A) → Maybe A

not : Bool → Bool
not true = false
not false = true

_or_ : Bool → Bool → Bool
true or y = true
false or y = y

if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

data Nat : Set where
  zero : Nat
  suc : Nat → Nat

{-# BUILTIN NATURAL Nat #-}

_+_ : Nat → Nat → Nat
zero + y = y
suc x + y = suc (x + y)

_*_ : Nat → Nat → Nat
zero * y = zero
suc x * y = y + (x * y)

_≡_ : Nat → Nat → Bool
zero ≡ zero = true
zero ≡ suc y = false
suc x ≡ zero = false
suc x ≡ suc y = x ≡ y

pred : Nat → Nat
pred zero = zero
pred (suc n) = n

mutual
  even : Nat → Bool
  even zero = true
  even (suc n) = odd n

  odd : Nat → Bool
  odd zero = false
  odd (suc n) = even n

n₂ : Nat
n₂ = suc (suc zero)

n₃ : Nat
n₃ = suc (suc (suc zero))

n₅ : Nat
n₅ = n₃ + n₂

n₁₅ : Nat
n₁₅ = n₅ * n₃

infixr 40 _::_

data List (A : Set) : Set where
  [] : List A
  _::_ : A → List A → List A

l : List Nat
l = n₂ :: n₃ :: n₅ :: n₁₅ :: []

the : (A : Set) → (x : A) → A
the A n = n

type : {A : Set} → (x : A) → Set
type {A} x = A

apply : (A : Set) → (B : A → Set) → ((x : A) → B x) → (a : A) → B a
apply A B f x = f x

id : {A : Set} → A → A
id x = x

_∘_ : {A : Set}{B : A → Set}{C : (x : A) → B x → Set}
      (f : {x : A}(y : B x) → C x y)
      (g : (x : A) → B x)
      (x : A) → C x (g x)
(f ∘ g) x = f (g x)

comp : (A : Set)(B : A → Set)(C : (x : A) → B x → Set)
       (f : {x : A}(y : B x) → C x y)
       (g : (x : A) → B x)
       (x : A) → C x (g x)
comp A B C f g x = f (g x)

{-
mutual 
  data A : Set where
    a : A
    toA : B → A

  data B : Set where
    b : B
    toB : A → B
    
r : A
r = comp A (λ _ → B) (λ x _ → A) toA toB a -}

map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x :: xs) = f x :: map f xs

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

l₂ : List Nat
l₂ = (map (_*_ three) l) ++ (map suc l)
  where three = (suc (suc (suc zero)))

data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _::_ : {n : Nat} → A → Vec A n → Vec A (suc n)

head : {A : Set} {n : Nat} → Vec A (suc n) → A
head (x :: xs) = x

vmap : {A B : Set} {n : Nat} → (A → B) → Vec A n → Vec B n
vmap f [] = []
vmap f (x :: xs) = f x :: vmap f xs

data Image_∋_ {A B : Set} (f : A → B) : B → Set where
  im : (x : A) → Image f ∋ f x

inv : {A B : Set} → (f : A → B) → (y : B) → Image f ∋ y → A
inv f .(f x) (im x) = x

--         ↓ результат ↓ то что мы можем подставить в (_ or true) чтобы его получить
r₁ : Bool
r₁ = inv f true (im false)
  where f = _or_ true

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc : {n : Nat} → Fin n → Fin (suc n)

magic : {A : Set} → Fin zero → A
magic ()

_!_ : {n : Nat} {A : Set} → Vec A n → Fin n → A
[] ! ()
(x :: xs) ! fzero = x
(x :: xs) ! fsuc fin = xs ! fin

r₂ : Bool
r₂ = xs ! (fsuc fzero)
  where xs = true :: false :: true :: false :: []        

tabulate : {n : Nat} {A : Set} → (Fin n → A) → Vec A n
tabulate {zero} f = []
tabulate {suc n} f = f fzero :: tabulate (f ∘ fsuc)

data False : Set where
record True : Set where

trivial : True
trivial = _

isTrue : Bool → Set
isTrue true = True
isTrue false = False

_<_ : Nat → Nat → Bool
_ < zero = false
zero < suc j = true
suc i < suc j = i < j

length : {A : Set} → List A → Nat
length [] = zero
length (x :: xs) = suc (length xs)

lookup : {A : Set} (xs : List A) (n : Nat) -> isTrue (n < length xs) -> A
lookup [] _ () 
lookup (x :: xs) zero p = x
lookup (x :: xs) (suc n) p = lookup xs n p

data _==_ {A : Set} (x : A) : A → Set where
  refl : x == x

data _≤_ : Nat → Nat → Set where
  leq-zero : {n : Nat} → zero ≤ n
  leq-suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

leq-trans : {l m n : Nat} -> l ≤ m -> m ≤ n -> l ≤ n
leq-trans leq-zero _ = leq-zero
leq-trans (leq-suc lm) (leq-suc mn) = leq-suc (leq-trans lm mn)

min : Nat → Nat → Nat
min x y with x < y
min x y | true = x
min x y | false = y

filter : {A : Set} → (A → Bool) → List A → List A
filter f [] = []
filter f (x :: xs) with f x
filter f (x :: xs) | true = x :: filter f xs
filter f (x :: xs) | false = xs

reverse : {α : Set} → List α → List α
reverse [] = []
reverse (x :: xs) = (reverse xs) ++ (x :: [])

_to_ : (x : Nat) → (y : Nat) → List Nat
x to y with x < y
x to y | true = {!!}
x to y | false = {!!}
