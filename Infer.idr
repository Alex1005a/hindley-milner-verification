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

Untypable : (env : Env n) -> (term : Term n) -> Type
Untypable env tm = (ty : Typ) -> (s : Subst) -> Not (substEnv s env |- (tm ::> ty))

MGT : Scope -> Env n -> Subst -> Term n -> Typ -> Type
MGT vars env s tm ty
    = (s0 : Subst)
    -> (ty0 : Typ)
    -> substEnv s0 env |- (tm ::> ty0)
    -> (s' ** ((ty' : Typ) -> TypeScope vars ty' -> (substType ty' s0 === substType ty' (s' + s)), ty0 === substType ty s'))

atIdx : (env, idx : _) -> AtIndex idx env (Vect.index idx env)
atIdx (x :: xs) FZ = Here
atIdx (x :: xs) (FS idx) = There $ atIdx xs idx

idxAll : {xs : Vect n a} -> (i : Fin n) -> All p xs -> p (index i xs)
idxAll FZ (px :: _) = px
idxAll (FS i) (_ :: all) = idxAll i all

substNotInScope : {i : _} -> (ty : Typ) -> TypeScope vars ty -> Not (Elem i vars) -> substType ty ((i, ty') :: s) === substType ty s
substNotInScope (TypVar v) (TSVar el) notEl =
    case decEq v i of
        Yes ok => absurd $ notEl (rewrite sym ok in el)
        No contra => rewrite notEqNatFalse contra in Refl
substNotInScope (argTy :-> retTy) (TSFun tsArg tsRet) notEl =
    rewrite substNotInScope {ty'} {s} argTy tsArg notEl in
    rewrite substNotInScope {ty'} {s} retTy tsRet notEl in
    Refl

substEnvNotInScope : {i : _} -> (env : Env n) -> All (TypeScope vars) env -> Not (Elem i vars) -> substEnv ((i, ty') :: s) env === substEnv s env
substEnvNotInScope [] [] notEl = Refl
substEnvNotInScope (ty :: env) (p :: ps) notEl =
    rewrite sym $ substEnvNotInScope {ty'} {s} env ps notEl in
    rewrite substNotInScope {ty'} {s} ty p notEl in
    Refl

substEnvScope : {svars : _} 
    -> {env : Env n}
    -> All (TypeScope vars) env
    -> All (flip Elem $ svars ++ vars') vars
    -> TypeScopeSubst svars vars' s
    -> All (TypeScope vars') (substEnv s env)
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

substEnvScopedRefl : {env : _}
    -> All (TypeScope vars) env
    -> ((ty' : Typ) -> TypeScope vars ty' -> substType ty' s = substType ty' s')
    -> substEnv s env === substEnv s' env
substEnvScopedRefl [] substRefl = Refl
substEnvScopedRefl {env = ty :: _} (scoped :: envScope) substRefl =
    rewrite substRefl ty scoped in
    rewrite substEnvScopedRefl {s} envScope substRefl in
    Refl

mgtVar' : {env : _} -> AtIndex idx (substEnv s0 env) ty0 -> ty0 === substType (index idx env) s0
mgtVar' {env = ty :: env} Here = Refl
mgtVar' {env = ty :: env} (There later) = mgtVar' later

mgtVar : {env : _} -> substEnv s0 env |- (Var idx ::> ty0) -> ty0 === substType (index idx env) s0
mgtVar (TVar at) = mgtVar' at

mgtAbs : {i : _}
    -> Not (Elem i vars)
    -> All (TypeScope vars) env
    -> MGT (i :: vars) (TypVar i :: env) s body ty
    -> MGT vars env s (Abs body) (substType (TypVar i) s :-> ty)
mgtAbs notEl allInScope mgtBody s0 (argTy :-> retTy) (TAbs {argTy} {retTy} r') =
    let (s' ** (substRefl, substEq)) = mgtBody ((i, argTy) :: s0) retTy
                    (rewrite equalNatReflTrue i in
                     rewrite substEnvNotInScope {s = s0} {ty' = argTy} {i} env allInScope notEl in r') in
    (s' ** rewrite sym $ composeSubst (TypVar i) s s' in
        (\ty => \inScope =>
            rewrite sym $ substNotInScope {s = s0} {ty' = argTy} {i} ty inScope notEl in
            substRefl ty (weakenScope {xs = []} {ys = [i]} inScope),
            rewrite sym $ substRefl (TypVar i) (TSVar Here) in
            rewrite equalNatReflTrue i in cong (argTy :->) substEq))

mgtApp : {n2, svars1, svars2, s1, s2, s3 : _}
    -> TypeScopeSubst svars1 varsFun s1
    -> TypeScopeSubst svars2 varsArg s2
    -> All (flip Elem (svars1 ++ varsFun)) vars
    -> All (flip Elem (svars2 ++ varsArg)) varsFun
    -> TypeScope varsFun funTy
    -> TypeScope varsArg argTy
    -> TypeScope varsArg (substType funTy s2)
    -> Not (Elem n2 varsArg)
    -> All (TypeScope vars) env
    -> MGT vars env s1 fun funTy
    -> MGT varsFun (substEnv s1 env) s2 arg argTy
    -> Unifiable (substType funTy s2) (argTy :-> TypVar n2) s3
    -> MGT vars env ((s3 + s2) + s1) (App fun arg) (substType (TypVar n2) s3)
mgtApp tsSub1 tsSub2 allEl allEl' ts1 ts2 funTys2ts notEl envScope mgt1 mgt2 mg s0 ty0 (TApp {argTy = argTy'} funRule argRule) =
    let (ss1 ** (substRefl, eqTy)) = mgt1 s0 (argTy' :-> ty0) funRule in
    let (ss2 ** (substRefl', eqTy2)) = mgt2 ss1 argTy'
            (rewrite sym $ composeSubstEnv env s1 ss1 in
             rewrite sym $ substEnvScopedRefl {s' = ss1 + s1} envScope substRefl in argRule) in
    let (ss3 ** substId3) = mg ((n2, ty0) :: ss2)  (rewrite substNotInScope {s = ss2} {ty' = ty0} {i = n2} _ funTys2ts notEl in
                                     rewrite sym $ composeSubst funTy s2 ss2 in
                                     rewrite sym $ substRefl' _ ts1 in
                                     rewrite sym eqTy in
                                     rewrite equalNatReflTrue n2 in
                                     rewrite eqTy2 in
                                     rewrite substNotInScope {s = ss2} {ty' = ty0} {i = n2} _ ts2 notEl in
                                     Refl) in
    (ss3 ** (\ty''' => \tyScope''' =>
        let subTys1Scope = substTypeScope _ allEl tyScope''' tsSub1 in
        rewrite substRefl  ty''' tyScope''' in
        rewrite composeSubst ty''' s1 ss1 in
        rewrite substRefl' (substType ty''' s1) subTys1Scope in
        rewrite composeSubst (substType ty''' s1) s2 ss2 in
        let subTys1s2Scope = substTypeScope _ allEl' subTys1Scope tsSub2 in
        rewrite sym $ substNotInScope {s = ss2} {ty' = ty0} {i = n2} _ subTys1s2Scope notEl in
        rewrite substId3 $ substType (substType ty''' s1) s2 in
        rewrite composeSubst ty''' ((s3 + s2) + s1) ss3 in
        rewrite composeSubst ty''' s1 (s3 + s2) in
        rewrite composeSubst (substType ty''' s1) s2 s3 in
        rewrite composeSubst (substType (substType ty''' s1) s2) s3 ss3 in
        Refl,
        rewrite sym $ composeSubst (TypVar n2) s3 ss3 in
        rewrite sym $ substId3 (TypVar n2) in
        rewrite equalNatReflTrue n2 in
        Refl))

lookupScope : {svars, idx : _}
    -> Elem idx (svars ++ vars')
    -> TypeScopeSubst svars vars' s
    -> TypeScope vars' (substType (TypVar idx) s)
lookupScope el [] = TSVar el
lookupScope el ((::) {i} ts tss) =
    case decEq (equalNat idx i) True of
        Yes ok =>
            rewrite ok in ts
        No contra =>
            rewrite notTrueFalse contra in
            case el of
                Here => absurd $ contra (rewrite equalNatReflTrue i in Refl)
                There later => lookupScope later tss

eqSubstEnv : All (TypeScope vars) env
    -> ((ty' : Typ) -> TypeScope vars ty' -> substType ty' s'' = substType ty' (s + ss))
    -> substEnv s'' env = substEnv (s + ss) env
eqSubstEnv [] mgt = Refl
eqSubstEnv (ts :: allInScope) mgt =
    rewrite mgt _ ts in
    rewrite eqSubstEnv {s''} allInScope mgt in
    Refl

inferW' : {vars : _}
    -> (term : Term n)
    -> (env : Env n)
    -> (tv : Nat)
    -> (alll : All (TypeScope vars) env)
    -> All (`LT` tv) vars
    -> Either (Untypable env term)
        (sub ** ty ** ntv ** svars ** vars' **
        (substEnv sub env |- (term ::> ty), TypeScope vars' ty, MGT vars env sub term ty, 
            All (flip Elem $ svars ++ vars') vars, TypeScopeSubst svars vars' sub, All (`LT` ntv) vars'))
inferW' (Var idx) env i allInScope allLT =
    pure ([] ** index idx env ** i ** [] ** vars **
        (rewrite substEnvId env in TVar $ atIdx env idx,
        idxAll idx allInScope,
        \s0 => \ty0 => \r' => (s0 ** (\_ => \_ => Refl, mgtVar r')),
        allElem vars, [], allLT))
inferW' (Abs body) env i allInScope allLT =
    let Right (sub ** retTy ** ni ** svars ** vars' ** (retRule, ts, mgt, (iel :: allEl), tsSub, nlt)) =
            inferW' body (TypVar i :: env) (S i)
                (TSVar Here :: mapProperty (weakenScope {xs = []} {ys = [i]}) allInScope)
                (reflexive :: mapProperty lteSuccRight allLT)
        | Left contra =>
            Left $ \ty' => \s' => \(TAbs {argTy} {retTy} r') =>
                contra _ ((i, argTy) :: s')
                    (rewrite equalNatReflTrue i in
                     rewrite substEnvNotInScope {s = s'} {ty' = argTy} {i} env allInScope (greaterAllNotEl _ allLT) in r') in
    pure (sub ** (substType (TypVar i) sub :-> retTy) ** ni ** svars ** vars' **
        (TAbs retRule, TSFun (lookupScope iel tsSub) ts,
         mgtAbs (greaterAllNotEl _ allLT) allInScope mgt,
         allEl, tsSub, nlt))
inferW' (App fun arg) env i allInScope allLT =
    let Right (s1 ** funTy ** n1 ** svars1 ** vars1' ** (funRule, ts1, mgt1, allEl1, tsSub1, nlt1)) = inferW' fun env i allInScope allLT
        | Left contra =>
            Left $ \_ => \s' => \(TApp rf ra) => 
            contra _ s' rf in
    let Right (s2 ** argTy ** n2 ** svars2 ** vars2' ** (argRule, ts2, mgt2, allEl2, tsSub2, nlt2))
            = inferW' arg (substEnv s1 env) n1 (substEnvScope allInScope allEl1 tsSub1) nlt1
        | Left contra =>
            Left $ \_ => \s'' => \(TApp rf ra) => 
            let (s ** (mgtTy', _)) = mgt1 s'' _ rf in
            let envEq : substEnv s'' env === substEnv (s + s1) env = eqSubstEnv {s''} allInScope mgtTy' in
            contra _ s (rewrite sym $ composeSubstEnv env s1 s in
                         rewrite sym envEq in ra) in
    let funTys2ts = substTypeScope _ allEl2 ts1 tsSub2 in
    let Right (s3 ** (scopeRel, eq, mg))
            = unifyAcc (substType funTy s2) (weakenScope {xs = []} {ys = [n2]} {zs = vars2'} funTys2ts)
                    (argTy :-> TypVar n2) (TSFun (weakenScope {xs = []} {ys = [n2]} {zs = vars2'} ts2) (TSVar Here) ) (wellFoundLex _ _)
        | Left contra =>
            Left $ \ty' => \s'' => \(TApp {argTy = argTy'} rf ra) =>
            let (s ** (mgtTy1, eq1)) = mgt1 s'' (argTy' :-> ty') rf in
            let envEq : substEnv s'' env === substEnv s (substEnv s1 env) =
                    rewrite sym $ composeSubstEnv env s1 s in
                    eqSubstEnv {s''} allInScope mgtTy1 in
            let (s' ** (mgtTy2, eq2)) = mgt2 s argTy' (rewrite sym envEq in ra) in
            contra ((n2, ty') :: s')
                (rewrite equalNatReflTrue n2 in
                 rewrite substNotInScope {s = s'} {ty'} {i = n2} argTy ts2 (greaterAllNotEl _ nlt2) in
                 rewrite substNotInScope {s = s'} {ty'} {i = n2} _ funTys2ts (greaterAllNotEl _ nlt2) in
                 rewrite sym eq2 in
                 rewrite sym $ composeSubst funTy s2 s' in
                 rewrite sym $ mgtTy2 _ ts1 in
                 rewrite sym eq1 in
                 Refl) in
    let newTss = (mapTypeSubst scopeRel.allEl (weakenSubstScope tsSub2) scopeRel.tyVarSub) ++ scopeRel.tyVarSub in
    let (n2el :: allVars2) = scopeRel.allEl in
    let newTss = mapTypeSubst (rewrite sym $ appendAssociative svars2 scopeRel.svars scopeRel.vars' in
                               allElemReplace allVars2 allEl2) tsSub1 newTss ++ newTss in
    let allEl = allElemReplace {ys = svars1 ++ svars2} allVars2 (rewrite sym $ appendAssociative svars1 svars2 vars2' in allElemReplace allEl2 allEl1) in
    pure ((s3 + s2) + s1 ** substType (TypVar n2) s3 ** S n2 ** _ ** _ **
        (rewrite composeSubstEnv env s1 (s3 + s2) in
        rewrite composeSubstEnv (substEnv s1 env) s2 s3 in
        TApp {argTy = substType argTy s3} (rewrite sym eq in substToRule s3 $ substToRule s2 funRule) (substToRule s3 argRule),
        lookupScope n2el scopeRel.tyVarSub,
        mgtApp tsSub1 tsSub2 allEl1 allEl2 ts1 ts2 funTys2ts (greaterAllNotEl _ nlt2) allInScope mgt1 mgt2 mg,
            rewrite appendAssociative svars1 svars2 scopeRel.svars in
            rewrite sym $ appendAssociative (svars1 ++ svars2) scopeRel.svars scopeRel.vars' in allEl, newTss,
            greaterAllStrengthen {xss = []} scopeRel.allElTyVars (reflexive :: mapProperty lteSuccRight nlt2)))

export
inferW : (tm : Term 0) -> Either (Untypable [] tm) (sub ** ty ** ([] |- (tm ::> ty), MGT [] [] sub tm ty))
inferW tm = do
    (sub ** ty ** ni ** svars ** vars' ** (rule, ts, mgt, allEl, tsSub, nlt)) <- inferW' {vars = []} tm [] 0 [] []
    pure (sub ** ty ** (rule, mgt))
        
