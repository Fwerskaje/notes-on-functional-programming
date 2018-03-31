{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Category where

import Pre hiding (id, (.))
import Monad
import Applicative

class Category arr where
  id  :: a `arr` a
  (.) :: b `arr` c -> a `arr` b -> a `arr` c

newtype Kleisli m a b = Kleisli {
  runKleisli :: a -> m b
}

instance Monad m => Category (Kleisli m) where
  id = Kleisli pure
  (Kleisli g) . (Kleisli h) = Kleisli (h >=> g)
  
class Category arr => Arrow arr where
  arr    :: (b -> c)    -> (b `arr` c)
  first  :: (b `arr` c) -> ((b, d) `arr` (c, d))
  second :: (b `arr` c) -> ((d, b) `arr` (d, c))
--  second a (x, y) = (
  (***)  :: (b `arr` c) -> (b' `arr` c') -> ((b, b') `arr` (c, c'))
  (&&&)  :: (b `arr` c) -> (b `arr` c')  -> (b `arr` (c, c'))

(>>>) :: Category arr => b `arr` c -> a `arr` b -> a `arr` c
g >>> f = g . f

instance Category (->) where
  id = (\x -> x)
  (.) g f x = g (f x)

--instance Arrow (->) where
--  arr g = g
--  first g (x, y) = (g x, y)

{-

:t arr ab
arr ab :: Arrow arr => arr A B

:t (arr ab) . (arr ba) | :t (arr ab) >>> (arr ba)
(arr ab) . (arr ba) :: Arrow arr => arr B B

:t (arr ab) *** (arr ba)
(arr ab) *** (arr ba) :: Arrow arr => arr (A, B) (B, A)

(g *** h) (x,y) = (g x, h y)

:t (arr ba) &&& (arr bc)
(arr ba) &&& (arr bc) :: Arrow arr => arr B (A, C)

(g &&& h) x = (g x, h x)

-}

