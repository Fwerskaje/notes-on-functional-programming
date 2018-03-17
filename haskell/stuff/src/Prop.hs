module Prop where

data Prop = Const Bool
          | Var Char
          | Not Prop
          | And Prop Prop
          | Imply Prop Prop

instance Show Prop where
  show (Const b) = show b
  show (Var c) = [c]
  show (Not p) = "not " ++ show p
  show (And p1 p2) = show p1 ++ " & " ++ show p2
  show (Imply p1 p2) = show p1 ++ " => " ++ show p2

p1 :: Prop
p1 = And (Var 'A') (Not (Var 'A'))

p2 :: Prop
p2 = Imply (And (Var 'A') (Var 'B')) (Var 'A')

type Assoc k v = [(k, v)]

type Subst = Assoc Char Bool

s :: Subst
s = [('A', True), ('B', False)]

eval :: Subst -> Prop -> Bool
eval _ (Const b) = b
eval s (Var c) = find c s
eval s (Not p) = not $ eval s p
eval s (And p1 p2) = (eval s p1) && (eval s p2)
eval s (Imply p1 p2) = (not (eval s p1)) || (eval s p2)

find :: Char -> Subst -> Bool
find c s = case lookup c s of
             Nothing -> False
             Just b -> b
