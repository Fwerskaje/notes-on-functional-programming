module IOMonad where

open import Data.String using (String; Costring; toCostring)
open import Data.Colist using (_++_)
open import IO.Primitive
open import Foreign.Haskell using (Unit; unit)

stringHello : Costring
stringHello = toCostring "Hello, "

postulate
  getLine : IO Costring

{-# COMPILE GHC getLine = getLine #-}

main : IO Unit
main = getLine >>= λ x →
       putStrLn (stringHello ++ x)

