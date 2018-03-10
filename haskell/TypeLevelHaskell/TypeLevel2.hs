{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module TypeLevel2 where

import GHC.TypeLits
import Data.Proxy

type family If c t e where
  If 'True t e = t
  If 'False t e = e

{-

:kind! If 'True Bool Char
If 'True Bool Char :: *
= Bool

:kind! If 'False Int Double
If 'False Int Double :: *
= Double

-}

