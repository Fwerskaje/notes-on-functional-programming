module G1 where

import Data.Monoid
import Data.Traversable
import Control.Applicative
import Data.Foldable

f1 :: Integer -> Integer
f1 = appEndo $ Endo (+1) <> Endo (+3)

e1 :: [Char]
e1 = "123" <> "456" <> "789"

e2 :: [Char]
e2 = getDual $ Dual "123" <> Dual "456" <> Dual "789"

e3 :: First Integer
e3 = foldMap First [Nothing, Just 42, Nothing, Just 3]

e4 :: Dual (First Integer)
e4 = foldMap (Dual . First) [Nothing, Just 42, Nothing, Just 3, Nothing]
--                                                      ^^^^^^ с конца

e5 :: Integer
e5 = (appEndo . getDual) (((Dual . Endo) (+5)) <> ((Dual . Endo) (*3))) 2

data Tree a = Nil | Branch (Tree a) a (Tree a)
  deriving (Eq, Show)

tree :: Tree Integer
tree = Branch (Branch Nil 3 (Branch (Branch Nil 3 Nil) 2 Nil)) 8 (Branch Nil 0 Nil)

instance Functor Tree where
  fmap f Nil = Nil
  fmap f (Branch l x r) = Branch (fmap f l) (f x) (fmap f r)

instance Foldable Tree where
  foldr f ini Nil = ini
  foldr f ini (Branch l x r) = f x (foldr f (foldr f ini r) l)

e6 :: Tree (Maybe Integer)
e6 = fmap Just tree

e7 :: Maybe Integer
e7 = asum e6

e8 :: Maybe ()
e8 = sequenceA_ e6

e9 :: Maybe ()
e9 = sequenceA_ [Just 3, Nothing, Just 4]

e10 :: Either a ()
e10 = sequenceA_ $ fmap Right tree

e11 :: Either Integer ()
e11 = sequenceA_ $ fmap Left tree

e12 :: ([Char], ())
e12 = sequenceA_ [("AB", 1), ("CD", 2)]

e13 :: (String, [Integer])
e13 = traverse (\x -> (show x ++ " doubled ", x * 2)) [1,2,3,4,5]

e14 :: IO ()
e14 = foldMap putStrLn $ map show [1..5]

e15 :: Either Integer ()
e15 = traverse_ (\x -> if x > 0 then Right x else Left x) $ [1..5] ++ [-1] ++ [5..6]
--                                                                    ^^^^
--                                                                   Left -1

e16 :: Either Integer ()
e16 = traverse_ (\x -> if x > 0 then Right x else Left x) $ [1..5] ++ [6,7]
-- Right ()

e17 :: Either Integer [Integer]
e17 = traverse (\x -> if x > 0 then Right x else Left x) $ [1..5] ++ [6,7]
-- Right [1,2,3,4,5,5,6]

e18 :: [[Integer]]
e18 = traverse (\x -> [x + 10, x + 20]) [1,2]
