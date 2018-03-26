{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}

module Tree where

data Tree a =
    Leaf a
  | Node [Tree a]
  deriving (Show, Functor, Foldable)

tree :: Tree Int
tree = Node [Leaf 3, Leaf 5, Leaf 6, Node [Leaf 3, Leaf 2]]
