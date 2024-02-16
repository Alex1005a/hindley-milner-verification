module Ext.List

import Data.Nat
import Ext.Nat
import Decidable.Equality
import Data.List
import Data.List.Elem
import Data.Maybe
import Ext.Basics

public export
lookup' : Eq a => a -> List (a, v) -> Maybe v
lookup' e [] = Nothing
lookup' e ((l, r) :: xs) =
  ifThenElse (e == l) (Just r) (lookup' e xs)

export
lookupSplit : (i : Nat) -> (s1, s2 : List (Nat, a)) -> lookup' i (s1 ++ s2) === (lookup' i s1) <+> (lookup' i s2)
lookupSplit i [] s2 = Refl
lookupSplit i ((l, s) :: s1) s2 =
    case decEq i l of
        Yes ok => rewrite ok in rewrite equalNatIdTrue l in Refl
        No contra =>
            rewrite notEqNatFalse contra in
            lookupSplit i s1 s2

export
lookupMap : (i : Nat)
    -> (f : a -> b)
    -> (xs : List (Nat, a))
    -> lookup' i xs === res
    -> lookup' i (map (bimap Prelude.id f) xs) === map f res
lookupMap i f [] Refl = Refl
lookupMap i f ((l, x) :: xs) prf =
    case decEq i l of
        Yes ok =>
            rewrite sym prf in
            rewrite ok in rewrite equalNatIdTrue l in Refl
        No contra =>
            rewrite notEqNatFalse contra in
            let prf' = replace {p = \b => ifThenElse b (Just x) (lookup' i xs) === res} (notEqNatFalse contra) prf in
            lookupMap i f xs prf'

public export
find' : (p : a -> Bool) -> (xs : List a) -> Maybe a
find' p [] = Nothing
find' p (x :: xs) = ifThenElse (p x) (Just x) (find' p xs)

export
isJustFindElem : {lst : List Nat} -> {n : _} -> Elem n lst -> IsJust (find' (== n) lst)
isJustFindElem {lst = l :: ll} el =
    case decEq l n of
        Yes Refl => rewrite equalNatIdTrue l in ItIsJust
        No contra => 
            rewrite notEqNatFalse contra in
            case el of
                Here => absurd $ contra Refl
                There later => isJustFindElem later

isJustFindAppend : {c : _} -> (xs : List a) -> IsJust (find' c xs) -> IsJust (find' c (xs ++ ys))
isJustFindAppend (x :: xs) isJustFind with (decEq (c x) True)
    isJustFindAppend (x :: xs) isJustFind | Yes ok =
        rewrite ok in
        replace {p = \g => IsJust (ifThenElse g (Just x)  (find' c xs))} ok isJustFind
    isJustFindAppend (x :: xs) isJustFind | No contra =
        rewrite notTrueFalse contra in
        let isJustFind' = replace {p = \b => IsJust (ifThenElse b (Just x) (find' c xs))} (notTrueFalse contra) isJustFind in
        isJustFindAppend _ isJustFind'

isJustFindPrepend : {c : _} -> (ys : List a) -> IsJust (find' c xs) -> IsJust (find' c (ys ++ xs))
isJustFindPrepend (y :: ys) isJustFind with (decEq (c y) True)
    isJustFindPrepend (y :: ys) isJustFind | Yes ok =
        rewrite ok in
        ItIsJust
    isJustFindPrepend (y :: ys) isJustFind | No contra =
        rewrite notTrueFalse contra in
        isJustFindPrepend _ isJustFind
isJustFindPrepend [] isJustFind = isJustFind

export
notFindSplit : {c : _} 
    -> {xs, ys : List a}
    -> Not (IsJust $ find' c (xs ++ ys)) -> ((Not $ IsJust (find' c xs)), (Not $ IsJust (find' c ys)))
notFindSplit notFind =
    (\isJustXs => notFind $ isJustFindAppend _ isJustXs,
     \isJustYs => notFind $ isJustFindPrepend _ isJustYs)

export
findSplit : {c : _} 
    -> {xs, ys : List a}
    -> IsJust (find' c (xs ++ ys)) -> Either (IsJust $ find' c xs) (IsJust $ find' c ys)
findSplit {xs = x :: xs} isJustFind with (decEq (c x) True)
    findSplit {xs = x :: xs} isJustFind | Yes ok =
        rewrite ok in
        Left ItIsJust
    findSplit {xs = x :: xs}isJustFind | No contra =
        rewrite notTrueFalse contra in
        let isJustFind' = replace {p = \b => IsJust (ifThenElse b (Just x) (find' c (xs ++ ys)))} (notTrueFalse contra) isJustFind in
        findSplit isJustFind'
findSplit {xs = []} isJustFind = Right isJustFind

export
lengthSDrop : (el : Elem i xs) -> S (length (dropElem xs el)) === length xs
lengthSDrop Here = Refl
lengthSDrop (There later) = cong S $ lengthSDrop later

export
lengthReplace : {ys, ys', zs : List a} 
    -> (xs : List a)
    -> length ys === length ys'
    -> length (xs ++ ys) === length zs
    -> length (xs ++ ys') === length zs
lengthReplace [] lenEq lenPlusEq = trans (sym lenEq) lenPlusEq
lengthReplace {zs = z :: zs} (x :: xs) lenEq lenPlusEq =
    let lenPlusEq' : length (xs ++ ys) === length zs =
            rewrite sym $ minusZeroRight (length (xs ++ ys)) in
            rewrite sym $ minusZeroRight (length zs) in
            cong (flip minus 1) lenPlusEq in
    cong S $ lengthReplace xs lenEq lenPlusEq'

export
lenghtLteIfEq : (xs, ys, zs : List a)
    -> {auto ok : NonEmpty xs}
        -> length (xs ++ ys) === length zs
        -> LT (length ys) (length zs)
lenghtLteIfEq (x :: xx :: xxs) ys (z :: zs) eq =
    let eq' : (length ((xx :: xxs) ++ ys)) === length zs =
        rewrite sym $ minusZeroRight (length zs) in
                cong (flip minus 1) eq in
    lteSuccRight $ lenghtLteIfEq (xx :: xxs) ys zs eq'
lenghtLteIfEq [x] ys zs eq = rewrite eq in reflexive
