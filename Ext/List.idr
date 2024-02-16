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
lookup' e ((k, v) :: xs) =
  ifThenElse (e == k) (Just v) (lookup' e xs)

export
lookupSplit : (e : Nat) -> (xs, ys : List (Nat, a)) -> lookup' e (xs ++ ys) === (lookup' e xs) <+> (lookup' e ys)
lookupSplit e [] ys = Refl
lookupSplit e ((k, _) :: xs) ys =
    case decEq e k of
        Yes ok =>
            rewrite ok in
            rewrite equalNatReflTrue k in
            Refl
        No contra =>
            rewrite notEqNatFalse contra in
            lookupSplit e xs ys

export
lookupMap : (e : Nat)
    -> (f : a -> b)
    -> (xs : List (Nat, a))
    -> lookup' e xs === res
    -> lookup' e (map (bimap Prelude.id f) xs) === map f res
lookupMap e f [] Refl = Refl
lookupMap e f ((l, x) :: xs) prf =
    case decEq e l of
        Yes ok =>
            rewrite sym prf in
            rewrite ok in
            rewrite equalNatReflTrue l in
            Refl
        No contra =>
            rewrite notEqNatFalse contra in
            let prf = replace {p = \b => ifThenElse b (Just x) (lookup' e xs) === res} (notEqNatFalse contra) prf in
            lookupMap e f xs prf

public export
find' : (a -> Bool) -> List a -> Maybe a
find' p [] = Nothing
find' p (x :: xs) = ifThenElse (p x) (Just x) (find' p xs)

export
isJustFindElem : {xs : List Nat} -> {n : _} -> Elem n xs -> IsJust (find' (== n) xs)
isJustFindElem {xs = x :: xs} el =
    case decEq x n of
        Yes Refl => rewrite equalNatReflTrue x in ItIsJust
        No contra => 
            rewrite notEqNatFalse contra in
            case el of
                Here => absurd $ contra Refl
                There later => isJustFindElem later

isJustFindAppend : {c : _} -> (xs : List a) -> IsJust (find' c xs) -> IsJust (find' c $ xs ++ ys)
isJustFindAppend (x :: xs) isJustFind with (decEq (c x) True)
    isJustFindAppend (x :: xs) isJustFind | Yes ok =
        rewrite ok in
        replace {p = \b => IsJust (ifThenElse b (Just x) (find' c xs))} ok isJustFind
    isJustFindAppend (x :: xs) isJustFind | No contra =
        rewrite notTrueFalse contra in
        let isJustFind' = replace {p = \b => IsJust (ifThenElse b (Just x) (find' c xs))} (notTrueFalse contra) isJustFind in
        isJustFindAppend _ isJustFind'

isJustFindPrepend : {c : _} -> (ys : List a) -> IsJust (find' c xs) -> IsJust (find' c $ ys ++ xs)
isJustFindPrepend (y :: ys) isJustFind with (decEq (c y) True)
    isJustFindPrepend (y :: ys) isJustFind | Yes ok =
        rewrite ok in
        ItIsJust
    isJustFindPrepend (y :: ys) isJustFind | No contra =
        rewrite notTrueFalse contra in
        isJustFindPrepend _ isJustFind
isJustFindPrepend [] isJustFind = isJustFind

export
notFindSplit : {c, xs, ys : _}
    -> Not (IsJust $ find' c (xs ++ ys))
    -> ((Not $ IsJust (find' c xs)), (Not $ IsJust (find' c ys)))
notFindSplit notFind =
    (\isJustXs => notFind $ isJustFindAppend _ isJustXs,
     \isJustYs => notFind $ isJustFindPrepend _ isJustYs)

export
findSplit : {c, xs, ys : _}
    -> IsJust (find' c (xs ++ ys))
    -> Either (IsJust $ find' c xs) (IsJust $ find' c ys)
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
lengthSuccDropEl : (el : Elem i xs) -> S (length $ dropElem xs el) === length xs
lengthSuccDropEl Here = Refl
lengthSuccDropEl (There later) = cong S $ lengthSuccDropEl later

export
lengthReplace : {ys, zs, xss : List a} 
    -> (xs : List a)
    -> length ys === length zs
    -> length (xs ++ ys) === length xss
    -> length (xs ++ zs) === length xss
lengthReplace [] lenEq lenPlusEq = trans (sym lenEq) lenPlusEq
lengthReplace {xss = _ :: xss} (x :: xs) lenEq lenPlusEq =
    let lenPlusEq : length (xs ++ ys) === length xss =
            rewrite sym $ minusZeroRight (length (xs ++ ys)) in
            rewrite sym $ minusZeroRight (length xss) in
            cong (flip minus 1) lenPlusEq in
    cong S $ lengthReplace xs lenEq lenPlusEq

export
lengthLTIfEqConcat : (xs, ys, zs : List a)
    -> {auto ok : NonEmpty xs}
    -> length (xs ++ ys) === length zs
    -> LT (length ys) (length zs)
lengthLTIfEqConcat (x :: y :: xs) ys (z :: zs) eq =
    let eq : (length ((y :: xs) ++ ys)) === length zs =
        rewrite sym $ minusZeroRight (length zs) in
            cong (flip minus 1) eq in
    lteSuccRight $ lengthLTIfEqConcat (y :: xs) ys zs eq
lengthLTIfEqConcat [x] ys zs eq = rewrite eq in reflexive
