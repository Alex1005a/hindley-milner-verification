module Ext.Nat

import Data.Nat

export
equalNatReflTrue : (n : Nat) -> equalNat n n === True
equalNatReflTrue Z = Refl
equalNatReflTrue (S n) = equalNatReflTrue n

export
notEqNatFalse : {i, n : Nat} -> Not (i === n) -> equalNat i n === False
notEqNatFalse notEq {i = Z} {n = Z} = absurd $ notEq Refl
notEqNatFalse notEq {i = Z} {n = S n} = Refl
notEqNatFalse notEq {i = S i} {n = Z} = Refl
notEqNatFalse notEq {i = S i} {n = S n} = rewrite notEqNatFalse (notEqS 1 notEq) in Refl
    where
    notEqS : (p : Nat) -> (p + i === p + n -> Void) -> (i === n -> Void)
    notEqS p notEq = \eq => notEq $ cong (plus p) eq

export
lteAddLeft : (n, m : Nat) -> LTE n (m + n)
lteAddLeft n Z = reflexive
lteAddLeft Z (S k)  = LTEZero
lteAddLeft (S n) (S k) =
    rewrite sym $ plusSuccRightSucc k n in 
    LTESucc $ lteAddLeft n (S k)

