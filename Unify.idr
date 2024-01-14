module Unify

import Lang
import Subst
import TypeScope
import Control.WellFounded
import Control.WellFounded.Lex
import Data.Maybe
import Data.Nat
import Data.List
import Data.List.Quantifiers
import Data.List.Elem
import Decidable.Equality
import Ext.Basics
import Ext.Nat
import Ext.List
import Ext.List.Elem

record TerminatRel (vars : List Nat) (sub : Subst) where
    constructor MkTR
    vars', svars : List Nat
    allEl : All (flip Elem $ svars ++ vars') vars
    lenEq : length (svars ++ vars') === length vars
    tyVarSub : TypeScopeSubst svars vars' sub

Sized Typ where
    size (TypVar _) = 1
    size (argTy :-> retTy) = S $ size argTy + size retTy

composeTR : {vars, s1 : _}
    -> (tr : TerminatRel vars s1)
    -> TerminatRel (tr.vars') s2
    -> TerminatRel vars (map (bimap Prelude.id $ flip Subst.substType s2) s1 ++ s2)
composeTR (MkTR vars' svars allEl lenEq tyScopeSub) (MkTR vars'' svars' allEl' lenEq' tyScopeSub') =
    MkTR vars'' (svars ++ svars')
        (rewrite sym $ appendAssociative svars svars' vars'' in allElemReplace allEl' allEl)
        (rewrite sym $ appendAssociative svars svars' vars'' in lengthReplace _ (sym lenEq') lenEq)
        ((mapTypeSubst allEl' tyScopeSub tyScopeSub') ++ tyScopeSub')

varBind : {vars : _}
    -> (var : Nat)
    -> Elem var vars
    -> (ty : Typ)
    -> TypeScope vars ty
    -> Maybe $ (sub ** (TerminatRel vars sub, substType (TypVar var) sub === substType ty sub))
varBind n nElVars (TypVar i) (TSVar iElVars) =
    case decEq i n of
        Yes ok => pure ([] ** (MkTR vars [] (allElem vars) Refl [], rewrite ok in Refl))
        No contra =>
            let iElDropVars = strengthenElem (\eq => contra $ sym eq) nElVars iElVars in
            pure ([(n, TypVar i)] ** (MkTR _ [n] (allElemDrop vars nElVars) (lengthSDrop nElVars) [TSVar iElDropVars],
                rewrite notEqNatFalse contra in
                rewrite equalNatIdTrue n in Refl))
varBind n nElVars ty ts =
    case isItJust $ find' (== n) (ftv ty) of
        Yes yes => Nothing
        No contra =>
            let notEl = notTrans isJustFindElem contra in
            pure $ ([(n, ty)] ** (MkTR _ [n] (allElemDrop vars nElVars) (lengthSDrop nElVars) [strengthenScope notEl nElVars ts],
                rewrite equalNatIdTrue n in
                rewrite substTyIdNoFtv ty ty n contra in
                Refl))

unifyAcc : {vars : _}
    -> (ty1 : Typ) -> TypeScope vars ty1
    -> (ty2 : Typ) -> TypeScope vars ty2
    -> SizeAccessLex (length vars, size ty1)
    -> Maybe (sub ** (TerminatRel vars sub, substType ty1 sub === substType ty2 sub))
unifyAcc (TypVar i) (TSVar iElVars) ty ts _ = varBind i iElVars ty ts
unifyAcc ty ts (TypVar i) (TSVar iElVars) _ = do
    (s ** (tr, prf)) <- varBind i iElVars ty ts
    pure (s ** (tr, sym prf))
unifyAcc (argTy1 :-> retTy1) (TSFun tsArg1 tsRet1) (argTy2 :-> retTy2) (TSFun tsArg2 tsRet2) sizeAcc@(Access rec) = do
    (s1 ** (tr1, prf1)) <- unifyAcc argTy1 tsArg1 argTy2 tsArg2 (rec _ $ Right $ LTESucc $ lteAddRight _)
    (s2 ** (tr2, prf2)) <- unifyAcc (substType retTy1 s1) (substTypeScope _ tr1.allEl tsRet1 tr1.tyVarSub)
            (substType retTy2 s1) (substTypeScope _ tr1.allEl tsRet2 tr1.tyVarSub)
            (rec _ $
                let (MkTR _ svars' _ leq tss) = tr1 in
                case svars' of
                    [] =>
                        rewrite leq in
                        let [] = tss in
                        rewrite substTypeId retTy1 in
                        Right $ LTESucc $ lteAddLeft _ _
                    (s :: ss) => Left $ lenghtLteIfEq (s :: ss) _ _ leq)
    pure (s2 + s1 ** (composeTR tr1 tr2,
        rewrite composeSubst retTy1 s1 s2 in
        rewrite composeSubst retTy2 s1 s2 in
        rewrite composeSubst argTy1 s1 s2 in
        rewrite composeSubst argTy2 s1 s2 in
        rewrite prf2 in
        rewrite cong (flip substType s2) prf1 in
        Refl))

export
unify : (ty1 : Typ) -> (ty2 : Typ) -> Maybe $ (sub ** substType ty1 sub === substType ty2 sub)
unify ty1 ty2 = do
    let (ts1, ts2) = commonScope (typeScopeFtv ty1) (typeScopeFtv ty2)
    (sub ** (_, prf)) <- unifyAcc ty1 ts1 ty2 ts2 (wellFoundLex _ _)
    pure (sub ** prf)
