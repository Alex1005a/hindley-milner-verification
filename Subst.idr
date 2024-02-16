module Subst

import Lang
import Data.Maybe
import Ext.List
import Ext.Nat
import Ext.Basics
import Data.Vect
import Data.Vect.AtIndex
import Decidable.Equality

Subst = List (Nat, Typ)

public export
substType : Typ -> Subst -> Typ
substType (TypVar i) sub = fromMaybe (TypVar i) $ lookup' i sub
substType (argTy :-> retTy) sub = substType argTy sub :-> substType retTy sub

public export
substEnv : Subst -> Env n -> Env n
substEnv sub env = map (flip substType sub) env

substAtIdx : AtIndex fi env ty -> AtIndex fi (substEnv sub env) (substType ty sub)
substAtIdx Here = Here
substAtIdx (There there) = There $ substAtIdx there

export
substToRule : (sub : Subst) -> env |- (term ::> ty) -> substEnv sub env |- (term ::> substType ty sub)
substToRule sub (TVar idx) = TVar $ substAtIdx idx
substToRule sub (TAbs body) = TAbs $ substToRule sub body
substToRule sub (TApp fun arg) = TApp (substToRule sub fun) (substToRule sub arg)

public export
(+) : Subst -> Subst -> Subst
(+) s1 s2 = map (bimap id $ flip substType s1) s2 ++ s1

export
composeSubst : (ty : Typ) -> (s1, s2 : Subst) -> substType ty (s2 + s1) === substType (substType ty s1) s2
composeSubst (TypVar v) s1 s2 =
    case isItJust $ lookup' v s1 of
        Yes ok =>
            let (r ** prf) = isJust _ ok in
            rewrite prf in 
            rewrite lookupSplit v (map (bimap id $ flip substType s2) s1) s2 in
            rewrite lookupMap v (flip substType s2) s1 prf in
            Refl
        No contra =>
            let prf = isNone _ contra in
            rewrite prf in 
            rewrite lookupSplit v (map (bimap id $ flip substType s2) s1) s2 in
            rewrite lookupMap v (flip substType s2) s1 prf in
            Refl
composeSubst (argTy :-> retTy) s1 s2 =
    rewrite composeSubst argTy s1 s2 in 
    rewrite composeSubst retTy s1 s2 in
    Refl

export
composeSubstEnv : (env : Env n) -> (s1, s2 : Subst) -> substEnv (s2 + s1) env === substEnv s2 (substEnv s1 env)
composeSubstEnv [] s1 s2 = Refl
composeSubstEnv (ty :: env) s1 s2 =
    rewrite composeSubst ty s1 s2 in
    rewrite composeSubstEnv env s1 s2 in
    Refl

export
substTypeId : (ty : Typ) -> substType ty [] === ty
substTypeId (TypVar v) = Refl
substTypeId (argTy :-> retTy) =
    rewrite substTypeId argTy in
    rewrite substTypeId retTy in
    Refl

export
substEnvId : (env : Env n) -> substEnv [] env === env
substEnvId (ty :: env) =
    rewrite substTypeId ty in
    rewrite substEnvId env in
    Refl
substEnvId [] = Refl

eqVarsNotNoFind : i === n -> Not (IsJust $ find' (== n) (ftv $ TypVar i)) -> Void
eqVarsNotNoFind eq notJust =
    let isJust : IsJust (find' (== n) (ftv $ TypVar i)) =
            rewrite eq in
            rewrite equalNatReflTrue n in ItIsJust in
    notJust isJust

export
substTyIdNoFtv : (ty, sty : Typ)
    -> (n : Nat) 
    -> Not (IsJust $ find' (== n) (ftv ty)) 
    -> substType ty [(n, sty)] === ty
substTyIdNoFtv (TypVar i) sty n notJust =
    case decEq i n of
        Yes ok => absurd $ eqVarsNotNoFind ok notJust
        No contra => rewrite notEqNatFalse contra in Refl
substTyIdNoFtv (a :-> r) sty n notJust =
    let (aftv, rftv) = notFindSplit {xs = ftv a} {ys = ftv r} notJust in
    rewrite substTyIdNoFtv a sty n aftv in
    rewrite substTyIdNoFtv r sty n rftv in
    Refl
