module Infer

import Lang
import TypeScope
import Data.Nat.Order.Properties
import Subst
import Unify
import Ext.List
import Ext.Nat
import Ext.Basics
import Ext.List.Elem
import Data.List.Elem
import Data.List.Quantifiers
import Data.Vect.Quantifiers
import Data.Vect
import Data.List
import Data.Vect.AtIndex
import Decidable.Equality
import Control.WellFounded
import Control.WellFounded.Lex

atIdx : (env, idx : _) -> AtIndex idx env (Vect.index idx env)
atIdx (x :: xs) FZ = Here
atIdx (x :: xs) (FS idx) = There $ atIdx xs idx

export
inferW : (term : Term n) -> (env : Env n) -> Nat -> Maybe ((sub ** ty ** (substEnv sub env |- (term ::> ty))), Nat)
inferW (Var idx) env i = pure (([] ** index idx env **
    rewrite substEnvId env in TVar $ atIdx env idx), i)
inferW (Abs body) env i = do
    ((sub ** retTy ** retRule), ni) <- inferW body (TypVar i :: env) (S i)
    pure ((sub ** ((substType (TypVar i) sub) :-> retTy) ** TAbs retRule), ni)
inferW (App fun arg) env i = do
    ((s1 ** funTy ** funRule), n1) <- inferW fun env i
    ((s2 ** argTy ** argRule), n2) <- inferW arg (substEnv s1 env) n1
    (s3 ** eq) <- unify (substType funTy s2) (argTy :-> (TypVar n2))
    pure (((s3 + s2) + s1 ** substType (TypVar n2) s3 **
        rewrite composeSubstEnv env s1 (s3 + s2) in
        rewrite composeSubstEnv (substEnv s1 env) s2 s3 in
        TApp {argTy = substType argTy s3} (rewrite sym eq in substToRule s3 $ substToRule s2 funRule) (substToRule s3 argRule)), S n2)

Untypable : (env : Env n) -> (term : Term n) -> Type
Untypable env tm = (ty : Typ) -> (s : Subst) -> Not (substEnv s env |- (tm ::> ty))

MGT : {vars : _} -> {env : Env n} -> Subst -> All (TypeScope vars) env -> Term n -> Typ -> Type
MGT {env} {vars} s _ tm ty = (s0 : Subst) -> (ty0 : Typ) -> substEnv s0 env |- (tm ::> ty0) -> (s' ** ((ty' : Typ) -> TypeScope vars ty' -> (substType ty' s0 === substType ty' (s' + s)), ty0 === substType ty s'))

substTyNotElWeaken : {i : _} -> (ty : Typ) -> TypeScope vars ty -> Not (Elem i vars) -> substType ty ((i, ty') :: s) === substType ty s
substTyNotElWeaken (TypVar v) (TSVar el) notEl =
    case decEq v i of
        Yes ok => absurd $ notEl (rewrite sym ok in el)
        No contra => rewrite notEqNatFalse contra in Refl
substTyNotElWeaken (argTy :-> retTy) (TSFun tsArg tsRet) notEl =
    rewrite substTyNotElWeaken {ty'} {s} argTy tsArg notEl in
    rewrite substTyNotElWeaken {ty'} {s} retTy tsRet notEl in
    Refl

substEnvNotElWeaken : {i : _} -> (env : Env n) -> All (TypeScope vars) env -> Not (Elem i vars) -> substEnv ((i, ty') :: s) env === substEnv s env
substEnvNotElWeaken [] [] notEl = Refl
substEnvNotElWeaken (ty :: env) (p :: ps) notEl =
    rewrite sym $ substEnvNotElWeaken {ty'} {s} env ps notEl in
    rewrite substTyNotElWeaken {ty'} {s} ty p notEl in
    Refl

substEnvScope : {svars : _} -> {env : Env n} -> All (TypeScope vars) env -> All (flip Elem $ svars ++ vars') vars -> TypeScopeSubst svars vars' s -> All (TypeScope vars') (substEnv s env)
substEnvScope [] allEl tss = []
substEnvScope (ts :: envTs) allEl tss' = substTypeScope _ allEl ts tss' :: substEnvScope envTs allEl tss'

greaterAllNotEl : {i : _} -> (xs : List Nat) -> All (`LT` i) xs -> Not (Elem i xs)
greaterAllNotEl [] [] = \case Refl impossible
greaterAllNotEl (x :: xs) (x_lt_i :: greaterAll) =
    let rec = greaterAllNotEl xs greaterAll in
    \case
        Here => absurd $ succNotLTEpred x_lt_i
        There later => absurd $ rec later

greaterAllStrengthen : {xss : List Nat}
    -> All (flip Elem zs) (xss ++ ys)
    -> All (`LT` i) zs -> All (`LT` i) ys
greaterAllStrengthen {xss = []} [] allLT = []
greaterAllStrengthen {xss = []} (el :: allEl) allLT =
    indexAll el allLT :: greaterAllStrengthen {xss = []} allEl allLT
greaterAllStrengthen {xss = _ :: xss} (_ :: allEl) allLT =
    greaterAllStrengthen allEl allLT

substEnvId : All (TypeScope vars) env -> ((ty'' : Typ) -> TypeScope vars ty'' -> substType ty'' s0 = substType ty'' s) -> substEnv s0 env === substEnv s env
substEnvId [] substId = Refl
substEnvId ((::) {x} {xs} scoped envScope) substId =
    rewrite substId x scoped in
    rewrite substEnvId {s0} envScope substId in
    Refl

mgtVar' : {env : _} -> AtIndex idx (substEnv s0 env) ty0 -> ty0 === substType (index idx env) s0
mgtVar' {env = ty :: env} Here = Refl
mgtVar' {env = ty :: env} (There later) = mgtVar' later

mgtVar : {env : _} -> substEnv s0 env |- (Var idx ::> ty0) -> ty0 === substType (index idx env) s0
mgtVar (TVar at) = mgtVar' at

mgtAbs : {i : _}
    -> Not (Elem i vars)
    -> All (TypeScope vars) env
    -> ((s00 : Subst) -> (ty00 : Typ) -> (substType (TypVar i) s00 :: substEnv s00 env) |- (body ::> ty00) -> (s' : Subst ** ((ty' : Typ) -> TypeScope (i :: vars) ty' -> (substType ty' s00 = substType ty' (s' + sub)) , ty00 = substType ty s')))
    -> (s0 : Subst) -> (ty0 : Typ) -> substEnv s0 env |- (Abs body ::> ty0)
    -> (s' : Subst ** ((ty' : Typ) -> TypeScope vars ty' -> (substType ty' s0 = substType ty' (s' + sub)), ty0 = substType (substType (TypVar i) sub) s' :-> substType ty s'))
mgtAbs notEl allScope mgtt s0 (argTy :-> retTy) (TAbs {argTy} {retTy} r') =
    let (s' ** (substId, retEqty')) = mgtt ((i, argTy) :: s0) retTy
                    (rewrite equalNatIdTrue i in
                     rewrite substEnvNotElWeaken {s = s0} {ty' = argTy} {i} env allScope notEl in r') in
    (s' ** rewrite sym $ composeSubst (TypVar i) sub s' in
        (\ttt => \scop =>
            rewrite sym $ substTyNotElWeaken {s = s0} {ty' = argTy} {i} ttt scop notEl in
            substId ttt (weakenScope {xs = []} {ys = [i]} scop),
            rewrite sym $ substId (TypVar i) (TSVar Here) in
            rewrite equalNatIdTrue i in cong (argTy :->) retEqty'))

mgtApp : {n2, svars1, svars2, s1, s2, s3 : _}
    -> TypeScopeSubst svars1 vars1' s1
    -> TypeScopeSubst svars2 vars2' s2
    -> All (flip Elem (svars1 ++ vars1')) vars
    -> All (flip Elem (svars2 ++ vars2')) vars1'
    -> TypeScope vars1' funTy
    -> TypeScope vars2' argTy
    -> TypeScope vars2' (substType funTy s2)
    -> Not (Elem n2 vars2')
    -> All (TypeScope vars) env
    -> ((s0' : Subst) -> (ty0' : Typ) -> substEnv s0' env |- (fun ::> ty0') -> (s'' : Subst ** ((ty'' : Typ) -> TypeScope vars ty'' -> substType ty'' s0' = substType ty'' (s'' + s1), ty0' = substType funTy s'')))
    -> ((s0'' : Subst) -> (ty0'' : Typ) -> substEnv s0'' (substEnv s1 env) |- (arg ::> ty0'') -> (s''' : Subst ** ((ty''' : Typ) -> TypeScope vars1' ty''' -> substType ty''' s0'' = substType ty''' (s''' + s2), ty0'' = substType argTy s''')))
    -> ((ss : Subst) -> substType (substType funTy s2) ss = substType argTy ss :-> substType (TypVar n2) ss -> (s' : Subst ** ((ty' : Typ) -> substType ty' ss = substType ty' (s' + s3))))
    -> (s0 : Subst)
    -> (ty0 : Typ)
    -> substEnv s0 env |- (App fun arg ::> ty0)
    -> (s' : Subst ** ((ty' : Typ) -> TypeScope vars ty' -> substType ty' s0 = substType ty' (s' + ((s3 + s2) + s1)), ty0 = substType (substType (TypVar n2) s3) s'))
mgtApp tsSub1 tsSub2 allEl1 allEl2 ts1 ts2 funTys2ts notEl envScope mgt1 mgt2 mg s0 ty0 (TApp {argTy = argTy'} funRule argRule) =
    let (ss1 ** (substId, eqTy)) = mgt1 s0 (argTy' :-> ty0) funRule in
    let (ss2 ** (substId2, eqTy2)) = mgt2 ss1 argTy'
            (rewrite sym $ composeSubstEnv env s1 ss1 in
             rewrite sym $ substEnvId {s = ss1 + s1} envScope substId in argRule) in
    let (ss3 ** substId3) = mg ((n2, ty0) :: ss2)  (rewrite substTyNotElWeaken {s = ss2} {ty' = ty0} {i = n2} _ funTys2ts notEl in
                                     rewrite sym $ composeSubst funTy s2 ss2 in
                                     rewrite sym $ substId2 _ ts1 in
                                     rewrite sym eqTy in
                                     rewrite equalNatIdTrue n2 in
                                     rewrite eqTy2 in
                                     rewrite substTyNotElWeaken {s = ss2} {ty' = ty0} {i = n2} _ ts2 notEl in
                                     Refl) in
    (ss3 ** (\ty''' => \tyScope''' =>
        let subTys1Scope = substTypeScope _ allEl1 tyScope''' tsSub1 in
        rewrite substId  ty''' tyScope''' in
        rewrite composeSubst ty''' s1 ss1 in
        rewrite substId2 (substType ty''' s1) subTys1Scope in
        rewrite composeSubst (substType ty''' s1) s2 ss2 in
        let subTys1s2Scope = substTypeScope _ allEl2 subTys1Scope tsSub2 in
        rewrite sym $ substTyNotElWeaken {s = ss2} {ty' = ty0} {i = n2} _ subTys1s2Scope notEl in
        rewrite substId3 $ substType (substType ty''' s1) s2 in
        rewrite composeSubst ty''' ((s3 + s2) + s1) ss3 in
        rewrite composeSubst ty''' s1 (s3 + s2) in
        rewrite composeSubst (substType ty''' s1) s2 s3 in
        rewrite composeSubst (substType (substType ty''' s1) s2) s3 ss3 in
        Refl,
        rewrite sym $ composeSubst (TypVar n2) s3 ss3 in
        rewrite sym $ substId3 (TypVar n2) in
        rewrite equalNatIdTrue n2 in
        Refl))

idxAll : {xs : Vect n a} -> (i : Fin n) -> All p xs -> p (index i xs)
idxAll FZ (px :: _) = px
idxAll (FS i) (_ :: all) = idxAll i all

lookupScope : {svars, idx : _} -> Elem idx (svars ++ vars') -> TypeScopeSubst svars vars' sub -> TypeScope vars' (fromMaybe (TypVar idx) (lookup' idx sub))
lookupScope el [] = TSVar el
lookupScope el ((::) {i} ts tss) =
    case decEq (equalNat idx i) True of
        Yes ok =>
            rewrite ok in ts
        No contra =>
            rewrite notTrueFalse contra in
            case el of
                Here => absurd $ contra (rewrite equalNatIdTrue i in Refl)
                There later => lookupScope later tss

inferW'' : {vars : _}
    -> (term : Term n)
    -> (env : Env n)
    -> (tv : Nat)
    -> (alll : All (TypeScope vars) env)
    -> All (`LT` tv) vars
    -> Maybe (sub ** ty ** ntv ** svars ** vars' ** (substEnv sub env |- (term ::> ty), TypeScope vars' ty, MGT sub alll term ty, All (flip Elem $ svars ++ vars') vars, TypeScopeSubst svars vars' sub, All (`LT` ntv) vars'))
inferW'' (Var idx) env i allScope allLT =
    pure ([] ** index idx env ** i ** [] ** vars **
        (rewrite substEnvId env in TVar $ atIdx env idx, idxAll idx allScope, \s0 => \ty0 => \r' => (s0 ** (\_ => \_ => Refl, mgtVar r')), allElem vars, [], allLT))
inferW'' (Abs body) env i allScope allLT = do
    (sub ** retTy ** ni ** svars ** vars' ** (retRule, ts, mgt, (iel :: allEl), tsSub, nlt)) <- inferW'' body (TypVar i :: env) (S i) {vars = i :: vars} (TSVar Here :: mapProperty (weakenScope {xs = []} {ys = [i]}) allScope) (reflexive :: mapProperty lteSuccRight allLT)
    pure (sub ** ((substType (TypVar i) sub) :-> retTy) ** ni ** svars ** vars' **
        (TAbs retRule, TSFun (lookupScope iel tsSub) ts,
         mgtAbs (greaterAllNotEl _ allLT) allScope mgt, allEl, tsSub, nlt))
inferW'' (App fun arg) env i allScope allLT = do
    (s1 ** funTy ** n1 ** svars1 ** vars1' ** (funRule, ts1, mgt1, allEl1, tsSub1, nlt1)) <- inferW'' fun env i allScope allLT
    (s2 ** argTy ** n2 ** svars2 ** vars2' ** (argRule, ts2, mgt2, allEl2, tsSub2, nlt2)) <- inferW'' arg (substEnv s1 env) n1 (substEnvScope allScope allEl1 tsSub1) nlt1
    let funTys2ts = substTypeScope _ allEl2 ts1 tsSub2
    (s3 ** (scopeRel, eq, mg)) <- unifyAcc (substType funTy s2) (weakenScope {xs = []} {ys = [n2]} {zs = vars2'} funTys2ts) (argTy :-> (TypVar n2)) (TSFun (weakenScope {xs = []} {ys = [n2]} {zs = vars2'} ts2) (TSVar Here) ) (wellFoundLex _ _)
    let newTss = (mapTypeSubst scopeRel.allEl (weakenSubstScope tsSub2) scopeRel.tyVarSub) ++ scopeRel.tyVarSub 
    let (n2el :: allVars2) = scopeRel.allEl
    let newTss = mapTypeSubst (rewrite sym $ appendAssociative svars2 scopeRel.svars scopeRel.vars' in
                               allElemReplace allVars2 allEl2) tsSub1 newTss ++ newTss
    let allll = allElemReplace {vars' = svars1 ++ svars2} allVars2 (rewrite sym $ appendAssociative svars1 svars2 vars2' in allElemReplace allEl2 allEl1)
    pure ((s3 + s2) + s1 ** substType (TypVar n2) s3 ** S n2 ** _ ** _ **
        (rewrite composeSubstEnv env s1 (s3 + s2) in
        rewrite composeSubstEnv (substEnv s1 env) s2 s3 in
        TApp {argTy = substType argTy s3} (rewrite sym eq in substToRule s3 $ substToRule s2 funRule) (substToRule s3 argRule), lookupScope n2el scopeRel.tyVarSub,
        mgtApp tsSub1 tsSub2 allEl1 allEl2 ts1 ts2 funTys2ts (greaterAllNotEl _ nlt2) allScope mgt1 mgt2 mg,
            rewrite appendAssociative svars1 svars2 scopeRel.svars in
            rewrite sym $ appendAssociative (svars1 ++ svars2) scopeRel.svars scopeRel.vars' in allll, newTss,
            greaterAllStrengthen {xss = []} scopeRel.allElTyVars (reflexive :: mapProperty lteSuccRight nlt2)))
