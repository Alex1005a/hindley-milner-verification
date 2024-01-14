module Ext.List.Elem

import Data.List.Elem
import Data.List.Quantifiers

export
strengthenElem : Not (v === n) -> (el : Elem v vars) -> Elem n vars -> Elem n (dropElem vars el)
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
elemNotEq : Not (Elem v (n :: ns)) -> Not (v === n)
elemNotEq notEl = \Refl => notEl Here

elemAdd : (lst' : _) -> Elem i (lst' ++ lst) -> Elem i (lst' ++ l :: lst)
elemAdd [] el = There el
elemAdd (ll :: lst') Here = Here
elemAdd (ll :: lst') (There later) = There $ elemAdd lst' later

elemPrepend : {lst' : _} -> Elem i lst -> Elem i (lst' ++ lst)
elemPrepend {lst' = []} el = el
elemPrepend {lst' = l :: lst'} el = There $ elemPrepend el

elemAppend :  Elem i lst -> Elem i (lst ++ lst')
elemAppend Here = Here
elemAppend (There later) = There $ elemAppend later

export
splitNotElem : {lst : _} -> Not (Elem v $ lst ++ lst') -> (Not $ Elem v lst, Not $ Elem v lst')
splitNotElem notEl = (\elLst => notEl $ elemAppend elLst, \elLst' => notEl $ elemPrepend elLst')

elemReplace : {vars' : _} -> Elem x (vars' ++ vars'') -> All (flip Elem vars''') vars'' -> Elem x (vars' ++ vars''')
elemReplace {vars' = y :: ys} Here all = Here
elemReplace {vars' = y :: ys} (There later) all = There $ elemReplace later all
elemReplace {vars' = []} (There later) (p :: ps) = elemReplace {vars' = []} later ps
elemReplace {vars' = []} Here (p :: ps) = p

export
allElem : (vars : List a) -> All (flip Elem vars) vars
allElem [] = []
allElem (x :: xs) = Here :: (mapProperty There $ allElem xs)

export
allElemDrop : {n : _} -> (vars : List a) -> (el : Elem n vars) -> All (flip Elem (n :: dropElem vars el)) vars
allElemDrop (x :: xs) Here = Here :: (mapProperty There $ allElem xs)
allElemDrop (x :: xs) (There later) =
    let rec = allElemDrop xs later in 
    There Here :: (mapProperty (elemAdd [n]) rec)

export
allElemReplace : {vars' : _}
    -> All (flip Elem vars''') vars''
    -> All (flip Elem (vars' ++ vars'')) vars
    -> All (flip Elem (vars' ++ vars''')) vars
allElemReplace all [] = []
allElemReplace all (x :: xs) = elemReplace x all :: allElemReplace all xs
