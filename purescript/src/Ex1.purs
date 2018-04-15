module Ex1 where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String as String

newtype Complex =
  Complex { real :: Number,
            imaginary :: Number }

cmplx :: Complex
cmplx = (Complex {real: 1.0, imaginary: 2.0})

instance showComplex :: Show Complex where
  show (Complex {real: r, imaginary: i}) =
    (show r) <> (op i) <> (show i) <> "i"
    where op n = if n < 0.0 then "" else "+"

instance eqComplex :: Eq Complex where
  eq (Complex {real: r1, imaginary: i1}) (Complex {real: r2, imaginary: i2}) =
    r1 == r2 && i1 == i2

class Stream stream element where
  uncons :: stream → Maybe { head :: element, tail :: stream }

instance streamArray :: Stream (Array a) a where
  uncons = Array.uncons
  
instance streamString :: Stream String Char where
  uncons = String.uncons

