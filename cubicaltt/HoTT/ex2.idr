module ex2

indProp : (x : Bool) -> Either (x = True) (x = False)
indProp False = Right Refl
indProp True = Left Refl

data N1 = Z1 | S1 N1
data N2 = Z2 | S2 N2
