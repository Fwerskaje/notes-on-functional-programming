module ex2

indProp : (x : Bool) -> Either (x = True) (x = False)
indProp False = Right Refl
indProp True = Left Refl

{-
CoproductFromSigma (A B : U) : U = Sigma Bool (recBool U A B)

exCoproduct : CoproductFromSigma Unit Unit = Sigma Bool ?
-}

CoproductFromSigma : (A : Type) -> (B : Type) -> (x : Bool) -> Type 
CoproductFromSigma a b x = (x ** if x then a else b)

