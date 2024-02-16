module Ext.List.Elem

import Data.List.Elem
import Data.List.Quantifiers

export
strengthenElem : Not (v === n) -> (el : Elem v xs) -> Elem n xs -> Elem n (dropElem xs el)
strengthenElem notEq Here Here = absurd $ notEq Refl
strengthenElem notEq (There later) Here = Here
strengthenElem notEq Here (There later') = later'
strengthenElem notEq (There later) (There later') = There $ strengthenElem notEq later later'

export
weakenElem : {xs, ys : _} -> Elem i (xs ++ zs) -> Elem i (xs ++ ys ++ zs)
weakenElem {xs = []} {ys = []} el = el
weakenElem {xs = []} {ys = y :: ys} el = There $ weakenElem {xs = []} el
weakenElem {xs = x :: xs} Here = Here
weakenElem {xs = x :: xs} (There later) = There $ weakenElem later

export
elemNotEq : Not (Elem x (y :: ys)) -> Not (x === y)
elemNotEq notEl = \Refl => notEl Here

elemAdd : (xs : _) -> Elem x (xs ++ ys) -> Elem x (xs ++ y :: ys)
elemAdd [] el = There el
elemAdd (_ :: xs) Here = Here
elemAdd (_ :: xs) (There later) = There $ elemAdd xs later

elemPrepend : {xs : _} -> Elem i ys -> Elem i (xs ++ ys)
elemPrepend {xs = []} el = el
elemPrepend {xs = l :: xs} el = There $ elemPrepend el

elemAppend :  Elem i xs -> Elem i (xs ++ ys)
elemAppend Here = Here
elemAppend (There later) = There $ elemAppend later

export
splitNotElem : {xs : _} -> Not (Elem v $ xs ++ ys) -> (Not $ Elem v xs, Not $ Elem v ys)
splitNotElem notEl = (\elys => notEl $ elemAppend elys, \elxs => notEl $ elemPrepend elxs)

elemReplace : {ys : _} -> Elem x (ys ++ zs) -> All (flip Elem zs') zs -> Elem x (ys ++ zs')
elemReplace {ys = y :: ys} Here all = Here
elemReplace {ys = y :: ys} (There later) all = There $ elemReplace later all
elemReplace {ys = []} (There later) (p :: ps) = elemReplace {ys = []} later ps
elemReplace {ys = []} Here (p :: ps) = p

export
allElem : (xs : List a) -> All (flip Elem xs) xs
allElem [] = []
allElem (x :: xs) = Here :: (mapProperty There $ allElem xs)

export
allElemToTop : {n : _} -> (xs : List a) -> (el : Elem n xs) -> All (flip Elem (n :: dropElem xs el)) xs
allElemToTop (x :: xs) Here = Here :: (mapProperty There $ allElem xs)
allElemToTop (x :: xs) (There later) =
    let rec = allElemToTop xs later in 
    There Here :: mapProperty (elemAdd [n]) rec

export
allElemReplace : {ys : _}
    -> All (flip Elem xs) zs
    -> All (flip Elem (ys ++ zs)) xxs
    -> All (flip Elem (ys ++ xs)) xxs
allElemReplace all [] = []
allElemReplace all (x :: xs) = elemReplace x all :: allElemReplace all xs
