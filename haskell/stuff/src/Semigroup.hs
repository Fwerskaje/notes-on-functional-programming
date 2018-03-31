{-# LANGUAGE NoImplicitPrelude #-}

module Semigroup where  

import Pre

class Semigroup a where
  (<>) :: a -> a -> a

instance Semigroup Int where
  (<>) = (+)

test1 :: Int
test1 = 3 <> (4 <> 5)

test2 :: Int
test2 = (3 + 4) + 5


