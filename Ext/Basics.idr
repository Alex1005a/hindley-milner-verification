module Ext.Basics

import Data.Maybe

export
notTrans : (b -> a) -> Not a -> Not b
notTrans f notA = notA . f

export
notTrueFalse : {x : _} -> Not (x === True) -> x === False
notTrueFalse {x = False} notTrue = Refl
notTrueFalse {x = True} notTrue = absurd $ notTrue Refl

export
isNone : (none : Maybe a) -> Not (IsJust none) -> none === Nothing
isNone Nothing prf = Refl
isNone (Just _) prf = absurd $ prf ItIsJust 

export
isJust : (just : Maybe a) -> IsJust just -> (val ** just === Just val)
isJust (Just v) ItIsJust = (v ** Refl)
