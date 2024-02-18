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

public export
Unifiable : Typ -> Typ -> Subst -> Type
Unifiable ty1 ty2 sub = (s0 : Subst) -> substType ty1 s0 === substType ty2 s0 -> (s' ** ((ty' : Typ) -> substType ty' s0 === substType ty' (s' + sub)))

Ununifiable ty1 ty2 = (s : Subst) -> Not (substType ty1 s === substType ty2 s)

public export
record ScopeRel (vars : Scope) (sub : Subst) where
    constructor MkTR
    vars', svars : Scope
    allEl : All (flip Elem $ svars ++ vars') vars
    allElTyVars : All (flip Elem vars) vars'
    lenEq : length (svars ++ vars') === length vars
    tyVarSub : TypeScopeSubst svars vars' sub

Sized Typ where
    size (TypVar _) = 1
    size (argTy :-> retTy) = S $ size argTy + size retTy

composeTR : {vars, s1 : _}
    -> (tr : ScopeRel vars s1)
    -> ScopeRel (tr.vars') s2
    -> ScopeRel vars (s2 + s1)
composeTR (MkTR vars' svars allEl allElTyVars lenEq tyScopeSub) (MkTR vars'' svars' allEl' allElTyVars' lenEq' tyScopeSub') =
    MkTR vars'' (svars ++ svars')
        (rewrite sym $ appendAssociative svars svars' vars'' in allElemReplace allEl' allEl)
        (allElemReplace {ys = []} allElTyVars allElTyVars')
        (rewrite sym $ appendAssociative svars svars' vars'' in lengthReplace _ (sym lenEq') lenEq)
        ((mapTypeSubst allEl' tyScopeSub tyScopeSub') ++ tyScopeSub')

substTypeVarId : {n : _} -> (tyt : Typ) -> (lookup' n s === Nothing) -> substType tyt s = substType tyt ((n, TypVar n) :: s)
substTypeVarId (TypVar v) lookNone =
    case decEq v n of
        Yes prf =>
            rewrite prf in
            rewrite lookNone in
            rewrite equalNatReflTrue n in
            Refl
        No contra =>
            rewrite notEqNatFalse contra in Refl
substTypeVarId (argTy :-> retTy) lookNone =
        rewrite substTypeVarId {s} argTy lookNone in 
        rewrite substTypeVarId {s} retTy lookNone in
        Refl

substTypeLook : {n : _} -> (tyt : Typ) -> lookup' n s === Just r -> substType tyt s = substType tyt ((n, r) :: s)
substTypeLook (TypVar v) lookJust =
    case decEq v n of
        Yes prf =>
            rewrite prf in
            rewrite equalNatReflTrue n in
            rewrite lookJust in
            Refl
        No contra =>
            rewrite notEqNatFalse contra in Refl
substTypeLook (argTy :-> retTy) lookJust =
        rewrite substTypeLook {s} argTy lookJust in 
        rewrite substTypeLook {s} retTy lookJust in
        Refl

allDrop : (el : Elem e xs) -> All p xs -> All p (dropElem xs el)
allDrop Here (_ :: all) = all
allDrop (There later) (p :: all) = p :: allDrop later all

isJustFtvTypVarRefl : {n, v : _} -> IsJust (find' (== n) (ftv (TypVar v))) -> n === v
isJustFtvTypVarRefl isJust =
    case decEq v n of
        Yes Refl => Refl
        No contra => absurd $ go (notEqNatFalse contra) isJust
    where
    go : (b === False) -> IsJust (ifThenElse b val (find' (== n) [])) -> Void
    go Refl isJ = uninhabited isJ

partT : {n : _} -> (ty : Typ) -> IsJust (find' (== n) (ftv ty)) -> (l ** PartType (TypVar n) l ty)
partT (TypVar v) isJust = let prf = isJustFtvTypVarRefl {n} {v} isJust in (0 ** rewrite prf in TyRefl)
partT (argTy :-> retTy) isJust =
    case findSplit isJust of
        Left isJust =>
            let (l ** prt) = partT _ isJust in
            (S l ** TyFunArg prt)
        Right isJust =>
            let (l ** prt) = partT _ isJust in
            (S l ** TyFunRet prt)

partTypeSubst : PartType ty' l ty -> PartType (substType ty' s) l (substType ty s)
partTypeSubst TyRefl = TyRefl
partTypeSubst (TyFunArg partTy) = TyFunArg $ partTypeSubst partTy
partTypeSubst (TyFunRet partTy) = TyFunRet $ partTypeSubst partTy

partTypeS : PartType (TypVar n) x (aty :-> rty) -> IsSucc x
partTypeS (TyFunArg partTy) = ItIsSucc
partTypeS (TyFunRet partTy) = ItIsSucc

varBind : {vars : _}
    -> (var : Nat)
    -> Elem var vars
    -> (ty : Typ)
    -> TypeScope vars ty
    -> Either (Ununifiable (TypVar var) ty) (sub ** (ScopeRel vars sub, substType (TypVar var) sub === substType ty sub, Unifiable (TypVar var) ty sub))
varBind n nElVars ty ts =
    case isItJust $ find' (== n) (ftv ty) of
        Yes yes =>
            case ty of
                (aty :-> rty) => 
                    Left $ \s => \eq =>
                        let (_ ** prt) = partT (aty :-> rty) yes in
                        let (ItIsSucc {n = n'}) = partTypeS prt in
                        let partTyEq = replace {p = \c => PartType (substType (TypVar n) s) (S n') c} (sym eq) $ partTypeSubst {s} prt in
                        partTypeSucc {ty = substType (TypVar n) s} partTyEq
                (TypVar v) =>
                    let prf = isJustFtvTypVarRefl {n} {v} yes in
                    pure ([] ** (MkTR vars [] (allElem vars) (allElem vars) Refl [], rewrite prf in Refl, \s => \eqq => (s ** \_ => Refl)))
        No contra =>
            let notEl = notTrans isJustFindElem contra in
            pure $ ([(n, ty)] **
               (MkTR _ [n] (allElemToTop vars nElVars) (allDrop _ $ allElem vars) (lengthSuccDropEl nElVars) [strengthenScope notEl nElVars ts],
                rewrite equalNatReflTrue n in
                rewrite substTyReflNoFtv ty ty n contra in
                Refl, \s => \eqq => (s **
                    rewrite sym eqq in
                    case isItJust $ lookup' n s of
                        Yes ok =>
                            \tyt => 
                                let (r ** prf) = isJust _ ok in
                                rewrite prf in 
                                rewrite substTypeLook {s} tyt prf in
                                Refl
                        No contra =>
                            \tyt => 
                                let prf = isNone _ contra in
                                rewrite prf in 
                                rewrite substTypeVarId {s} tyt prf in
                                Refl)))

funTyElemsEq : (x1 :-> y1) === (x2 :-> y2) -> (x1 === x2, y1 === y2)
funTyElemsEq Refl = (Refl, Refl)

export
unifyAcc : {vars : _}
    -> (ty1 : Typ) -> TypeScope vars ty1
    -> (ty2 : Typ) -> TypeScope vars ty2
    -> SizeAccessLex (length vars, size ty1)
    -> Either (Ununifiable ty1 ty2) (sub ** (ScopeRel vars sub, substType ty1 sub === substType ty2 sub, Unifiable ty1 ty2 sub)) 
unifyAcc (TypVar i) (TSVar iElVars) ty ts _ = varBind i iElVars ty ts 
unifyAcc ty ts (TypVar i) (TSVar iElVars) _ = do
    case varBind i iElVars ty ts of
        Right (s ** (tr, prf, substId)) => pure (s ** (tr, sym prf, \s' => \eqq => substId s' $ sym eqq))
        Left contra => Left $ \s => \eq => contra s (sym eq)
unifyAcc (argTy1 :-> retTy1) (TSFun tsArg1 tsRet1) (argTy2 :-> retTy2) (TSFun tsArg2 tsRet2) sizeAcc@(Access rec) =
    let Right (s1 ** (tr1, prf1, mg1)) = unifyAcc argTy1 tsArg1 argTy2 tsArg2 (rec _ $ Right $ LTESucc $ lteAddRight _)
        | Left contra =>
            Left $ \s => \eq =>
            contra s (rewrite fst $ funTyElemsEq eq in Refl) in
    let Right (s2 ** (tr2, prf2, mg2)) = unifyAcc (substType retTy1 s1) (substTypeScope _ tr1.allEl tsRet1 tr1.tyVarSub)
            (substType retTy2 s1) (substTypeScope _ tr1.allEl tsRet2 tr1.tyVarSub)
            (rec _ $
                let (MkTR _ svars' _ _ leq tss) = tr1 in
                case svars' of
                    [] =>
                        rewrite leq in
                        let [] = tss in
                        rewrite substTypeId retTy1 in
                        Right $ LTESucc $ lteAddLeft _ _
                    (s :: ss) => Left $ lengthLTIfEqConcat (s :: ss) _ _ leq)
        | Left contra =>
            Left $ \s => \eq =>
            let (eqSubArg, eqSubRet) = funTyElemsEq eq in
            let (s' ** mgtTy') = mg1 s eqSubArg  in
            contra s' (rewrite sym $ composeSubst retTy1 s1 s' in
                       rewrite sym $ composeSubst retTy2 s1 s' in
                       rewrite sym $ mgtTy' retTy1 in
                       rewrite sym $ mgtTy' retTy2 in
                       eqSubRet) in
    pure (s2 + s1 ** (composeTR tr1 tr2,
        rewrite composeSubst retTy1 s1 s2 in
        rewrite composeSubst retTy2 s1 s2 in
        rewrite composeSubst argTy1 s1 s2 in
        rewrite composeSubst argTy2 s1 s2 in
        rewrite prf2 in
        rewrite cong (flip substType s2) prf1 in
        Refl,
        \s => \eqq =>
            let (argEq, retEq) = funTyElemsEq eqq in
            let (s' ** eq1) = mg1 s argEq in
            let (s'' ** eq2) = mg2 s'
                    (rewrite sym $ composeSubst retTy1 s1 s' in
                     rewrite sym $ eq1 retTy1 in
                     rewrite sym $ composeSubst retTy2 s1 s' in
                     rewrite sym $ eq1 retTy2 in
                     retEq) in
            the (s' : Subst ** (ty' : Typ) -> substType ty' s = substType ty' (s' + (s2 + s1)))
            (s'' ** \ty' =>
                rewrite composeSubst ty' (s2 + s1) s'' in
                rewrite composeSubst ty' s1 s2 in
                rewrite sym $ composeSubst (substType ty' s1) s2 s'' in
                rewrite sym $ eq2 (substType ty' s1) in
                rewrite eq1 ty' in
                rewrite composeSubst ty' s1 s' in
                Refl)))

export
unify : (ty1 : Typ) -> (ty2 : Typ) -> Maybe $ (sub ** substType ty1 sub === substType ty2 sub)
unify ty1 ty2 = do
    let (ts1, ts2) = commonScope (typeScopeFtv ty1) (typeScopeFtv ty2)
    let Right (sub ** (_, prf, _)) = unifyAcc ty1 ts1 ty2 ts2 (wellFoundLex _ _)
        | Left _ => Nothing
    pure (sub ** prf)
