module TypeScope

import Lang
import Subst
import Data.Maybe
import Data.List
import Data.List.Quantifiers
import Data.List.Elem
import Ext.Nat
import Ext.List
import Ext.List.Elem
import Decidable.Equality

public export
data TypeScope : List Nat -> Typ -> Type where
    TSVar : Elem n vars -> TypeScope vars (TypVar n)
    TSFun : TypeScope vars argTy -> TypeScope vars retTy -> TypeScope vars (argTy :-> retTy)

public export
data TypeScopeSubst : List Nat -> List Nat -> Subst -> Type where
    Nil : TypeScopeSubst [] vars []
    (::) : TypeScope vars ty -> TypeScopeSubst svars' vars sub -> TypeScopeSubst (i :: svars') vars ((i, ty) :: sub)

export
typeScopeRename : All (flip Elem $ vars') vars -> TypeScope vars ty -> TypeScope vars' ty
typeScopeRename prf (TSVar vElVars) = TSVar $ indexAll vElVars prf
typeScopeRename prf (TSFun tvArg tvFun) = TSFun (typeScopeRename prf tvArg) (typeScopeRename prf tvFun)

substTypeScope' : {svars : _}
    -> (ty : Typ)
    -> TypeScope (svars ++ vars') ty
    -> TypeScopeSubst svars vars' s
    -> TypeScope vars' (substType ty s)
substTypeScope' (TypVar v) ts [] = ts
substTypeScope' {svars = i :: svars'} (TypVar v) (TSVar vElVars) (ts :: tss) =
    case decEq v i of
        Yes ok =>
            rewrite ok in rewrite equalNatReflTrue i in ts
        No contra =>
            rewrite notEqNatFalse contra in
            case vElVars of
                Here => absurd $ contra Refl
                There later => substTypeScope' (TypVar v) (TSVar later) tss
substTypeScope' (argTy :-> retTy) (TSFun tsArg tsRet) tss = TSFun (substTypeScope' argTy tsArg tss) (substTypeScope' retTy tsRet tss)

export
substTypeScope : {svars : _}
    -> (ty : Typ)
    -> All (flip Elem $ svars ++ vars') vars
    -> TypeScope vars ty
    -> TypeScopeSubst svars vars' s
    -> TypeScope vars' (substType ty s)
substTypeScope ty prf ts tss = substTypeScope' ty (typeScopeRename prf ts) tss

export
strengthenScope : {ty : _} -> Not (Elem v $ ftv ty) -> (el : Elem v vars) -> TypeScope vars ty -> TypeScope (dropElem vars el) ty
strengthenScope notElFtv vElVars (TSVar nElVars) =
    let v_notEq_n = elemNotEq notElFtv in
    TSVar $ strengthenElem v_notEq_n vElVars nElVars
strengthenScope notElFtv vElVars (TSFun tsArg tsRet) =
    let (notElArgFtv, notElFunFtv) = splitNotElem notElFtv in
    let recArg = strengthenScope notElArgFtv vElVars tsArg in 
    let recRet = strengthenScope notElFunFtv vElVars tsRet in 
    TSFun recArg recRet

export
weakenScope : {xs, ys : _} -> TypeScope (xs ++ zs) ty -> TypeScope (xs ++ ys ++ zs) ty
weakenScope (TSVar nElVars) = TSVar $ weakenElem nElVars
weakenScope (TSFun tsArg tsRet) = TSFun (weakenScope tsArg) (weakenScope tsRet)

export
weakenSubstScope : {x : _} -> TypeScopeSubst svars vars' s -> TypeScopeSubst svars (x :: vars') s
weakenSubstScope [] = []
weakenSubstScope (ts :: tss) = weakenScope {xs = []} {ys = [x]} {zs = vars'} ts :: weakenSubstScope tss

export
typeScopeFtv : (ty : Typ) -> TypeScope (ftv ty) ty
typeScopeFtv (TypVar v) = TSVar Here
typeScopeFtv (argTy :-> retTy) =
    let recArg = weakenScope {xs = ftv argTy} {zs = []} $ 
                 rewrite appendNilRightNeutral (ftv argTy) in typeScopeFtv argTy in
    let recFun = weakenScope {xs = []} {ys = ftv argTy} {zs = ftv retTy} $ typeScopeFtv retTy in
    TSFun (rewrite sym $ appendNilRightNeutral (ftv retTy) in recArg) recFun

export
commonScope : {vars, vars', ty, ty' : _}
    -> TypeScope vars ty
    -> TypeScope vars' ty'
    -> (TypeScope (vars ++ vars') ty, TypeScope (vars ++ vars') ty')
commonScope tv tv' =
    let newTv = weakenScope {xs = vars} {zs = []} $ 
                rewrite appendNilRightNeutral vars in tv in
    (rewrite sym $ appendNilRightNeutral vars' in newTv, weakenScope {xs = []} {ys = vars} {zs = vars'} tv')

export
mapTypeSubst : {svars', sub : _}
    -> All (flip Elem $ svars' ++ vars'') vars'
    -> TypeScopeSubst svars vars' sub
    -> TypeScopeSubst svars' vars'' sub'
    -> TypeScopeSubst svars vars'' (map (bimap Prelude.id $ flip Subst.substType sub') sub)
mapTypeSubst allEl [] tvs = []
mapTypeSubst allEl (ts :: tss) tss' = substTypeScope _ allEl ts tss' :: mapTypeSubst allEl tss tss'

export
(++) : TypeScopeSubst svars vars' sub -> TypeScopeSubst svars' vars' sub' -> TypeScopeSubst (svars ++ svars') vars' (sub ++ sub')
[] ++ tss = tss
(ts :: tss) ++ tss' = ts :: tss ++ tss'
