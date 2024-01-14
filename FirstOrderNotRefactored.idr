module FirstOrderNotRefactored

import Data.Fin
import Decidable.Equality
import Control.WellFounded
import Data.Vect
import Data.Vect.AtIndex

%default total

data Typ : Nat -> Type where
    TyVar : Fin n -> Typ n
    TyFun : Typ n -> Typ n -> Typ n

data Subst : Nat -> Nat -> Type where
    Nil : Subst n n
    Snoc : Subst m n -> Typ m -> Fin (S m) -> Subst (S m) n

lteSubst : {m : _} -> Subst m n -> LTE n m
lteSubst (Snoc s _ _) = lteSuccRight $ lteSubst s
lteSubst Nil = reflexive

0 ltIfNotEq : (Not $ m === n) -> Subst m n -> LT n m
ltIfNotEq prf (Snoc Nil _ _) = reflexive
ltIfNotEq prf (Snoc s@(Snoc {}) _ _) = LTESucc $ lteSubst s 
ltIfNotEq prf Nil = absurd $ prf Refl
    
compose : Subst l m -> Subst m n -> Subst l n
compose Nil s = s
compose (Snoc s' ty v) s = Snoc (compose s' s) ty v

thick : {n : Nat} -> Fin (S n) -> Fin (S n) -> Maybe (Fin n)
thick FZ FZ   = Nothing
thick FZ (FS y) = Just y
thick {n = S _} (FS x) FZ = Just FZ
thick {n = S _} (FS x) (FS y) = FS <$> (thick x y)

mutual 
    applySub : {m : Nat} -> (s : Subst m n) -> Typ m -> Typ n
    applySub s (TyVar v) = applySubFin s v
    applySub s (TyFun argTy funTy) = TyFun (applySub s argTy) (applySub s funTy)

    applySubFin : {m : Nat} -> (s : Subst m n) -> Fin m -> Typ n
    applySubFin Nil v = TyVar v
    applySubFin (Snoc s ty f) v =
        case thick f v of
            Just v' => applySubFin s v'
            Nothing => applySub s ty

isJust : {j : Maybe a} -> IsJust j -> (res ** j === Just res)
isJust {j = Just r} prf = (r ** Refl)

isNone : {none : Maybe a} -> (Not $ IsJust none) -> none === Nothing
isNone {none = Nothing} isJustVoid = Refl
isNone {none = Just _} isJustVoid = absurd $ isJustVoid ItIsJust


0 thickId : thick x x === Nothing
thickId {x = FZ} = Refl
thickId {x = FS FZ} = Refl
thickId {x = FS x@(FS _)} = cong (map FS) $ thickId {x}

0 mapNothing : (Not $ IsJust (map f none)) -> Not $ IsJust none
mapNothing {none = Just _} isJustVoid = absurd $ isJustVoid ItIsJust
mapNothing {none = Nothing} isJustVoid = \case Refl impossible

thickIdIfNothing : {n : _} -> {x, y : Fin (S n)} -> (Not $ IsJust (thick x y)) -> x === y
thickIdIfNothing {x = FZ} {y = FZ} isJustVoid = Refl
thickIdIfNothing {n = S _} {x = FS x} {y = FZ} isJustVoid = absurd $ isJustVoid ItIsJust
thickIdIfNothing {x = FZ} {y = FS y} isJustVoid = absurd $ isJustVoid ItIsJust
thickIdIfNothing {n = S _} {x = FS x} {y = FS y} isJustVoid = cong FS (thickIdIfNothing {x} {y} $ mapNothing isJustVoid)

occurCheck : {n : Nat} -> (x : Fin (S n)) -> (ty : Typ (S n)) -> Maybe (ty' : Typ n ** (0 anyTy : Typ n) -> applySub [] ty' === applySub (Snoc [] anyTy x) ty)
occurCheck x1 (TyVar x2) =
    case isItJust $ thick x1 x2 of
        Yes ok =>
            let (v ** prf) = isJust ok in
            pure (TyVar v **
                rewrite prf in
                \_ => Refl)
        No contra => Nothing
occurCheck x1 (TyFun argTy funTy) = do
    (argTy' ** prf1) <- occurCheck x1 argTy
    (funTy' ** prf2) <- occurCheck x1 funTy
    pure (TyFun argTy' funTy' ** prf prf1 prf2)
    where
    prf : ((0 anyTy1 : Typ n) -> applySub [] argTy' = applySub (Snoc [] anyTy1 x1) argTy) ->
        ((0 anyTy2 : Typ n) -> applySub [] funTy' = applySub (Snoc [] anyTy2 x1) funTy) ->
        (0 anyTy : Typ n) -> TyFun (applySub [] argTy') (applySub [] funTy') = TyFun (applySub (Snoc [] anyTy x1) argTy) (applySub (Snoc [] anyTy x1) funTy)
    prf prf1 prf2 anyTy = rewrite prf1 anyTy in rewrite prf2 anyTy in Refl

flexRigid : {n : Nat} -> (x : Fin n) -> (ty : Typ n) -> Maybe (m2 ** s : Subst n m2 ** applySubFin s x === applySub s ty)
flexRigid {n = S n} x ty =
    case occurCheck x ty of
        Nothing => Nothing
        Just (ty' ** prf) => Just (n ** Snoc Nil ty' x ** rewrite thickId {x} in prf ty')

flexFlex : {n : Nat} -> (x1 : Fin n) -> (x2 : Fin n) -> (m2 ** s : Subst n m2 ** applySubFin s x1 = applySubFin s x2)
flexFlex {n = S n} x y =
    case isItJust $ thick x y of
        Yes ok =>
            let (z ** prf) = isJust ok in
            (n ** Snoc Nil (TyVar z) x **
                rewrite prf in
                rewrite thickId {x} in
                Refl)
        No contra => (S n ** Nil ** rewrite thickIdIfNothing {x} {y} contra in Refl)
    

mutual
    0 composeSubFin : applySub acc2 (applySubFin acc1 v) = applySubFin (compose acc1 acc2) v
    composeSubFin {acc1 = Nil} = Refl
    composeSubFin {acc1 = Snoc acc1 ty i} =
        case isItJust $ thick i v of
            Yes ok =>
                let (v ** prf) = isJust ok in
                rewrite prf in
                composeSubFin {acc1} {acc2} {v}
            No contra =>
                rewrite isNone contra in
                composeSubst {acc1} {acc2} {ty}

    0 composeSubst : applySub acc2 (applySub acc1 ty) === applySub (compose acc1 acc2) ty
    composeSubst {ty = TyVar v} = composeSubFin {acc1} {acc2} {v}
    composeSubst {ty = TyFun argTy funTy} =
        rewrite composeSubst {ty = argTy} {acc1} {acc2} in 
        rewrite composeSubst {ty = funTy} {acc1} {acc2} in
        Refl

0 applySubNil : applySub [] ty === ty
applySubNil {ty = TyVar v} = Refl
applySubNil {ty = TyFun argTy funTy} =
    rewrite applySubNil {ty = argTy} in
    rewrite applySubNil {ty = funTy} in
    Refl

notEqIfLteS : S m = n -> LTE n m -> Not $ S m === n
notEqIfLteS prf LTEZero = \case Refl impossible
notEqIfLteS {m = S m} {n = S n} prf (LTESucc lte) =
    \ll =>
        let prf' : S m === n = rewrite sym $ minusZeroRight n in cong (flip minus 1) prf in
        notEqIfLteS prf' lte prf'

substNil : (s : Subst m n) -> (refl : m === n) -> applySub s ty = applySub s ty' -> ty === ty'
substNil Nil Refl ok = rewrite sym $ applySubNil {ty} in rewrite sym $ applySubNil {ty = ty'} in ok
substNil (Snoc s@(Snoc {}) _ _) prf _ =
    void $ notEqIfLteS prf (lteSubst s) prf

unify : {m : _} -> (ty1 : Typ m) -> (ty2 : Typ m) -> (0 _ : SizeAccessible m) -> Maybe (m2 ** s : Subst m m2 ** applySub s ty1 === applySub s ty2)
unify (TyFun argTy funTy) (TyFun argTy' funTy') sizeAcc@(Access rec) = do
    (m1 ** acc' ** prf1) <- unify argTy argTy' sizeAcc
    case decEq m m1 of
        Yes ok => do
            (m2 ** acc'' ** prf2) <- unify funTy funTy' sizeAcc
            pure (m2 ** acc'' **
                    rewrite prf2 in
                    rewrite substNil {ty = argTy} {ty' = argTy'} acc' ok prf1 in
                    Refl)
        No contra => do
            (m2 ** acc'' ** prf2) <- unify (applySub acc' funTy) (applySub acc' funTy') (rec _ (ltIfNotEq contra acc'))
            pure (m2 ** compose acc' acc'' **
                    rewrite sym $ composeSubst {acc1 = acc'} {acc2 = acc''} {ty = argTy} in
                    rewrite sym $ composeSubst {acc1 = acc'} {acc2 = acc''} {ty = argTy'} in
                    rewrite sym $ composeSubst {acc1 = acc'} {acc2 = acc''} {ty = funTy} in
                    rewrite sym $ composeSubst {acc1 = acc'} {acc2 = acc''} {ty = funTy'} in
                    rewrite prf2 in
                    rewrite cong (applySub acc'') prf1 in 
                    Refl)
unify (TyVar x1) (TyVar x2) _ = Just $ flexFlex x1 x2
unify (TyVar x1) t2 _ = flexRigid x1 t2
unify t1 (TyVar x2) _ = do
    (m1 ** acc ** prf) <- flexRigid x2 t1
    pure (m1 ** acc ** sym prf)

data Term : Nat -> Type where
    Var : Fin n -> Term n
    App : Term n -> Term n -> Term n
    Abs : Term (S n) -> Term n

Context = \n => \m => Vect n (Typ m)

infix 10 |-
infix 11 ::>

data TypedT : Nat -> Nat -> Type where
    (::>) : Term n -> Typ m -> TypedT n m

data (|-) : Context n m -> TypedT n m -> Type where

    TVar : AtIndex fi env ty ->
        ---------------------------
        env |- Var fi ::> ty

    TApp : (env |- fun ::> TyFun tyArg tyRet)
        -> (env |- arg ::> tyArg) ->
        ---------------------------
        env |- App fun arg ::> tyRet

    TAbs : {tyArg : Typ m} 
        -> (tyArg :: env) |- body ::> tyRet ->
        ---------------------------
        env |- Abs body ::> TyFun tyArg tyRet

data ParLTE : LTE n m -> LTE l p -> Type where
    ReflP : ParLTE lte lte
    StepP : ParLTE lte1 lte2 -> ParLTE (LTESucc lte1) lte2

parLteZero : (lte : LTE n (n + m)) -> (lte2 : LTE 0 m) -> ParLTE lte lte2
parLteZero LTEZero LTEZero = ReflP
parLteZero (LTESucc lte) lte2 = StepP $ parLteZero lte lte2

lteParLte : {l' : _} -> {lte1 : LTE l' m'} -> {lte2 : LTE l m} -> ParLTE lte1 lte2 -> LTE l l'
lteParLte ReflP = reflexive
lteParLte (StepP s) = lteSuccRight $ lteParLte s

parLteRefl : (lte1 : LTE l m') -> (lte2 : LTE l m) -> ParLTE lte1 lte2 -> m' === m
parLteRefl _ _ ReflP = Refl
parLteRefl _ _ (StepP s) = void $ succNotLTEpred $ lteParLte s

succPar : ParLTE lte1 lte2 -> ParLTE (LTESucc lte1) (LTESucc lte2)
succPar ReflP = ReflP
succPar (StepP parLte) = StepP $ succPar parLte

parLteMinus : {l : _} -> (lte2 : LTE m n) -> LTE m l -> (lte1 : LTE l (n + (l `minus` m)) ** ParLTE lte1 lte2)
parLteMinus lte2 LTEZero =
    rewrite minusZeroRight l in 
    rewrite plusCommutative n l in
    (lteAddRight l ** parLteZero _ lte2)
parLteMinus (LTESucc lte2') (LTESucc m_lte_l) =
    let (lte1 ** parLte) = parLteMinus lte2' m_lte_l in (LTESucc lte1 ** succPar parLte)

parLteSub : {l, m, n : _} -> Subst l m -> (lte2 : LTE m n) -> (l' ** lte1 : LTE l l' ** ParLTE lte1 lte2)
parLteSub sub lte2 =
    let lte3 = lteSubst sub in
    let (lte4 ** parLte) = parLteMinus lte2 lte3 in
    (_ ** lte4 ** parLte)

weakenTyp : LTE m m1 -> Typ m -> Typ m1
weakenTyp m_lte_m1 (TyVar v) = TyVar $ weakenLTE v m_lte_m1
weakenTyp m_lte_m1 (TyFun argTy funTy) = TyFun (weakenTyp m_lte_m1 argTy) (weakenTyp m_lte_m1 funTy)

weakenEnv : LTE m m1 -> Context l m -> Context l m1
weakenEnv m_lte_m1 env = weakenTyp m_lte_m1 <$> env

weakenSub : (lte1 : LTE m m') -> (lte2 : LTE l l') -> ParLTE lte2 lte1 -> Subst l m -> Subst l' m'
weakenSub lte1 lte2 parLte [] = rewrite parLteRefl lte2 lte1 parLte in []
weakenSub lte1 (LTESucc lte2) (StepP parLte) (Snoc s ty v) =
    let recs = weakenSub lte1 lte2 parLte s in
    Snoc recs (weakenTyp lte2 ty) (weakenLTE v $ LTESucc lte2)
weakenSub _ _ ReflP (Snoc s _ _) = void $ succNotLTEpred $ lteSubst s

applySubEnv : {m : _} -> Subst m n -> Context l m -> Context l n
applySubEnv sub [] = []
applySubEnv sub (ty :: env) = applySub sub ty :: applySubEnv sub env

applySubEnvNil : {env : Context l m} -> applySubEnv [] env === env
applySubEnvNil {env = []} = Refl
applySubEnvNil {env = ty :: env} =
    rewrite applySubEnvNil {env} in
    rewrite applySubNil {ty} in
    Refl

natToFinS : (m : Nat) -> Fin (S m)
natToFinS Z = FZ
natToFinS (S m) = FS $ natToFinS m

0 weakenLTENested : weakenLTE v lte = weakenLTE (weakenLTE v lte2) lte1
weakenLTENested {v = FZ} {lte = LTESucc lte} {lte1 = LTESucc lte1} {lte2 = LTESucc lte2} = Refl
weakenLTENested {v = FS v} {lte = LTESucc lte} {lte1 = LTESucc lte1} {lte2 = LTESucc lte2} =
    cong FS $ weakenLTENested {v} {lte} {lte1} {lte2}

0 weakenNested : weakenTyp lte ty === weakenTyp lte1 (weakenTyp lte2 ty)
weakenNested {ty = TyVar v} = rewrite weakenLTENested {v} {lte} {lte1} {lte2} in Refl
weakenNested {ty = TyFun argTy funTy} =
    rewrite weakenNested {lte} {lte1} {lte2} {ty = argTy} in
    rewrite weakenNested {lte} {lte1} {lte2} {ty = funTy} in
    Refl

0 composeSubstEnv : applySubEnv (compose acc1 acc2) env === applySubEnv acc2 (applySubEnv acc1 env)
composeSubstEnv {env = []} = Refl
composeSubstEnv {env = ty :: env} =
    rewrite sym $ composeSubst {acc1} {acc2} {ty} in
    rewrite composeSubstEnv {acc1} {acc2} {env} in
    Refl

weakenLteFZ : {lte1, lte2 : _} -> weakenLTE FZ lte1 = weakenLTE FZ lte2
weakenLteFZ {lte1 = LTESucc LTEZero} {lte2 = LTESucc lte2} = Refl
weakenLteFZ {lte1 = LTESucc $ LTESucc lte1} {lte2 = LTESucc lte2} = Refl

0 weakenLteTrans : weakenLTE (weakenLTE v lte3) lte1 === weakenLTE v (transitive lte3 lte2)
weakenLteTrans {v = FZ} {lte3 = LTESucc lte3} = weakenLteFZ {lte1} {lte2 = transitive (LTESucc lte3) lte2}
weakenLteTrans {v = FS v} {lte3 = LTESucc lte3} {lte1 = LTESucc lte1} {lte2 = LTESucc lte2} =
    cong FS $ weakenLteTrans {v} {lte3} {lte1} {lte2}

fromLteSucc' : LTE (S m) (S n) -> LTE m n
fromLteSucc' (LTESucc x) = x

eqSucc : (f1 : Maybe (Fin n)) -> (f2 : Maybe (Fin m)) -> map (\c => weakenLTE c lte) f1 === f2 -> map (\c => weakenLTE c (LTESucc lte)) (map FS f1) === map FS f2
eqSucc (Just f1) (Just f2) prf = cong (map FS) prf
eqSucc Nothing Nothing prf = Refl

thickWeakenEq : {n : Nat} -> (f1, f2 : Fin (S n)) -> {lte : LTE (S n) (S m)} -> ((\c => weakenLTE c (fromLteSucc' lte)) <$> thick f1 f2) === (thick (weakenLTE f1 lte) (weakenLTE f2 lte))
thickWeakenEq FZ FZ {lte = LTESucc lte} = Refl
thickWeakenEq FZ (FS y) {lte = LTESucc lte} = Refl
thickWeakenEq {n = S _} (FS x) FZ  {lte = LTESucc $ LTESucc lte} = Refl
thickWeakenEq {n = S _} {lte = LTESucc $ LTESucc lte} (FS x) (FS y) =
    let rec = thickWeakenEq {lte = LTESucc lte} x y in
    rewrite sym $ eqSucc _ _ rec in
    Refl

0 transtiveRefl : (reflLte : LTE x x) -> lte === transitive reflLte lte
transtiveRefl {lte = LTEZero} LTEZero = Refl
transtiveRefl {lte = LTESucc lte} (LTESucc reflLte) = cong LTESucc $ transtiveRefl {lte} reflLte

weakenLTERefl : (v : Fin x) -> (reflLte : LTE x x) -> v === weakenLTE v reflLte
weakenLTERefl FZ (LTESucc reflLte) = Refl
weakenLTERefl (FS v) (LTESucc reflLte) = cong FS $ weakenLTERefl v reflLte


weakenTypRefl : (ty : Typ x) -> (reflLte : LTE x x) -> ty === weakenTyp reflLte ty
weakenTypRefl (TyVar v) reflLte = rewrite sym $ weakenLTERefl v reflLte in Refl
weakenTypRefl (TyFun argTy funTy) reflLte = 
    rewrite sym $ weakenTypRefl argTy reflLte in
    rewrite sym $ weakenTypRefl funTy reflLte in
    Refl

0 weakenTypTrans : weakenTyp lte1 (weakenTyp lte3 ty) === weakenTyp (transitive lte3 lte2) ty
weakenTypTrans {ty = TyVar v} = rewrite weakenLteTrans {v} {lte3} {lte1} {lte2} in Refl
weakenTypTrans {ty = TyFun argTy funTy} =
    rewrite weakenTypTrans {ty = argTy} {lte1} {lte2} {lte3} in
    rewrite weakenTypTrans {ty = funTy} {lte1} {lte2} {lte3} in
    Refl

mutual
    0 applyFinWeaken : {parLte, sub : _} -> applySubFin (weakenSub lte1 lte2 parLte sub) (weakenLTE v (transitive lte3 lte2)) === weakenTyp lte1 (applySubFin sub (weakenLTE v lte3))
    applyFinWeaken {sub = []} {parLte = ReflP} = cong TyVar $ sym $ weakenLteTrans {v} {lte3} {lte1} {lte2 = lte1}
    applyFinWeaken {sub = []} {parLte = StepP s} = void $ succNotLTEpred $ lteParLte s
    applyFinWeaken {parLte = ReflP} {sub = Snoc s _ _} = void $ succNotLTEpred $ lteSubst s
    applyFinWeaken {sub = Snoc sub ty i} {lte2 = LTESucc lte2} {parLte = StepP parLte} =
        rewrite sym $ weakenLteTrans {v} {lte3} {lte1 = LTESucc lte2} {lte2 = LTESucc lte2} in
        rewrite sym $ thickWeakenEq {lte = LTESucc lte2} i (weakenLTE v lte3) in
        case isItJust $ thick i (weakenLTE v lte3) of
            Yes ok =>
                let (v ** prf) = isJust ok in
                rewrite prf in
                rewrite weakenLTERefl v reflexive in
                rewrite weakenLteTrans {v} {lte3 = reflexive} {lte1 = lte2} {lte2} in
                applyFinWeaken {lte1} {lte2} {parLte} {sub} {v} {lte3 = reflexive}
            No contra =>
                rewrite isNone contra in
                rewrite weakenTypRefl ty reflexive in
                rewrite weakenTypTrans {ty} {lte3 = reflexive} {lte1 = lte2} {lte2} in
                applyWeakenSub {lte1} {lte2} {parLte} {sub} {ty} {lte3 = reflexive}

    0 applyWeakenSub : {ty : _} -> applySub (weakenSub lte1 lte2 parLte sub) (weakenTyp (transitive lte3 lte2) ty) === weakenTyp lte1 (applySub sub (weakenTyp lte3 ty))
    applyWeakenSub {ty = TyVar v} = applyFinWeaken {lte1} {lte2} {parLte} {sub} {v} {lte3}
    applyWeakenSub {ty = TyFun argTy funTy} =
        rewrite applyWeakenSub {ty = argTy} {lte1} {lte2} {lte3} {parLte} {sub} in
        rewrite applyWeakenSub {ty = funTy} {lte1} {lte2} {lte3} {parLte} {sub} in
        Refl

applyWeakenMap : {env : Context l m} -> applySubEnv (weakenSub lte1 lte2 parLte sub) (map (weakenTyp (transitive lte3 lte2)) env) === map (weakenTyp lte1) (applySubEnv sub (map (weakenTyp lte3) env))
applyWeakenMap {env = []} = Refl
applyWeakenMap {env = ty :: env} = 
    rewrite applyWeakenMap {lte1} {lte2} {lte3} {parLte} {sub} {env} in
    rewrite applyWeakenSub {lte1} {lte2} {parLte} {sub} {ty} {lte3} in
    Refl

weakenTypSuccRight : (ty : Typ m) -> weakenTyp lte (weakenTyp (lteSuccRight $ reflexive_Reflexive_Nat_LTE {x = m}) ty) === weakenTyp (lteSuccLeft lte) ty
weakenTypSuccRight (TyVar v) = rewrite weakenLTENested {v} {lte1 = lte} {lte2 = lteSuccRight reflexive} {lte = lteSuccLeft lte} in Refl
weakenTypSuccRight (TyFun argTy funTy) =
    rewrite weakenTypSuccRight {lte} argTy in
    rewrite weakenTypSuccRight {lte} funTy in
    Refl

weakenEnvSuccRight : {env : Context l m} -> map (weakenTyp lte) (map (weakenTyp (lteSuccRight $ reflexive_Reflexive_Nat_LTE {x = m})) env) === map (weakenTyp (lteSuccLeft lte)) env
weakenEnvSuccRight {env = []} = Refl
weakenEnvSuccRight {env = ty :: env} =
    rewrite weakenEnvSuccRight {env} {lte} in
    rewrite weakenTypSuccRight ty {lte} in
    Refl

substAtIdx : AtIndex fi env ty -> AtIndex fi (applySubEnv sub env) (applySub sub ty)
substAtIdx Here = Here
substAtIdx (There there) = There $ substAtIdx there

applySubRule : {m : _} -> {0 ty : Typ m} -> {0 env : Context l m} -> (sub : Subst m n) -> env |- (term ::> ty) -> applySubEnv sub env |- (term ::> applySub sub ty)
applySubRule sub (TVar idx) = TVar $ substAtIdx idx
applySubRule sub (TAbs body) = TAbs $ applySubRule sub body
applySubRule sub (TApp fun arg) = TApp (applySubRule sub fun) (applySubRule sub arg)

weakenAtIdx : {0 env : Context l m} -> AtIndex fi env ty -> AtIndex fi (map (weakenTyp lte) env) (weakenTyp lte ty)
weakenAtIdx Here = Here
weakenAtIdx (There there) = There $ weakenAtIdx there

weakenRule : {m : _} -> {0 ty : Typ m} -> {0 env : Context l m} -> {lte : LTE m n} -> env |- (term ::> ty) -> map (weakenTyp lte) env |- (term ::> weakenTyp lte ty)
weakenRule (TVar idx) = TVar $ weakenAtIdx idx
weakenRule (TAbs body) = TAbs $ weakenRule body
weakenRule (TApp fun arg) = TApp (weakenRule fun) (weakenRule arg)

weakenEnvRefl : {env : Context l m} -> map (weakenTyp $ reflexive_Reflexive_Nat_LTE {x = m}) env === env
weakenEnvRefl {env = []} = Refl
weakenEnvRefl {env = ty :: env} =
    rewrite sym $ weakenTypRefl ty reflexive in
    rewrite weakenEnvRefl {env} in
    Refl

atIdx : (env, idx : _) -> AtIndex idx env (Vect.index idx env)
atIdx (x :: xs) FZ = Here
atIdx (x :: xs) (FS idx) = There $ atIdx xs idx

inferW : {m : _} -> (term : Term n) -> (env : Context n m) 
    -> Maybe (m1 ** m_lte_m1 : LTE m m1 ** m2 ** sub : Subst m1 m2 ** ty ** (applySubEnv sub (weakenEnv m_lte_m1 env) |- (term ::> ty)))
inferW (Var idx) env =
    pure (m ** reflexive ** m ** [] ** index idx env 
        ** TVar $ rewrite weakenEnvRefl {env} in rewrite applySubEnvNil {env} in atIdx env idx)
inferW (Abs body) env = do
    (m1 ** sm_lte_m1 ** m2 ** sub ** retTy ** retRule) <- inferW body (TyVar (natToFinS m) :: weakenEnv (lteSuccRight reflexive) env) {m = S m}
    pure (m1 ** lteSuccLeft sm_lte_m1 ** m2 ** sub ** TyFun (applySubFin sub $ weakenLTE (natToFinS m) sm_lte_m1) retTy ** 
            TAbs $ rewrite sym $ weakenEnvSuccRight {env} {lte = sm_lte_m1} in retRule)
inferW (App fun arg) env = do
    (m1 ** m_lte_m1 ** m2 ** sub ** funTy ** funRule) <- inferW fun env
    (m1' ** m_lte_m1' ** m2' ** sub' ** argTy ** argRule) <- inferW arg (applySubEnv sub (weakenEnv m_lte_m1 env))
    (m2'' ** sub'' ** prf) <- unify (weakenTyp (lteSuccRight reflexive) $ applySub sub' $ weakenTyp m_lte_m1' funTy) (TyFun (weakenTyp (lteSuccRight reflexive) argTy) (TyVar $ natToFinS m2')) (wellFounded $ S m2')
    let (m1'' ** m1_lte_m1'' ** parLte) = parLteSub sub m_lte_m1'
    let (m1''' ** m1''_lte_m1''' ** parLte') = parLteSub ((weakenSub _ _ parLte sub) `compose` sub') (lteSuccRight reflexive)

    let prf1 : (map (weakenTyp (lteSuccRight reflexive)) $ applySubEnv sub' (map (weakenTyp m_lte_m1') (applySubEnv sub (map (weakenTyp m_lte_m1) env))))
                === applySubEnv (weakenSub (lteSuccRight reflexive) m1''_lte_m1''' parLte' (compose (weakenSub m_lte_m1' m1_lte_m1'' parLte sub) sub')) (map (weakenTyp $ transitive (transitive m_lte_m1 m1_lte_m1'') m1''_lte_m1''') env) =
                rewrite applyWeakenMap {lte1 = lteSuccRight reflexive} {sub = compose (weakenSub m_lte_m1' m1_lte_m1'' parLte sub) sub'} {parLte = parLte'} {env} {lte3 = transitive m_lte_m1 m1_lte_m1''} {lte2 = m1''_lte_m1'''} in
                rewrite composeSubstEnv {acc1 = weakenSub m_lte_m1' m1_lte_m1'' parLte sub} {acc2 = sub'} {env = map (weakenTyp (transitive m_lte_m1 m1_lte_m1'')) env} in
                rewrite applyWeakenMap {lte1 = m_lte_m1'} {sub} {parLte} {env} {lte3 = m_lte_m1} {lte2 = m1_lte_m1''} in Refl
    
    pure (_ ** transitive (transitive m_lte_m1 m1_lte_m1'') m1''_lte_m1''' ** _ 
            ** (weakenSub _ _ parLte' ((weakenSub _ _ parLte sub) `compose` sub')) `compose` sub''
            ** applySub sub'' (TyVar $ natToFinS m2') ** 
            rewrite composeSubstEnv {acc1 = weakenSub (lteSuccRight reflexive) m1''_lte_m1''' parLte' (compose (weakenSub m_lte_m1' m1_lte_m1'' parLte sub) sub')}
                            {acc2 = sub''} {env = map (weakenTyp $ transitive (transitive m_lte_m1 m1_lte_m1'') m1''_lte_m1''') env} in
            rewrite sym prf1 in
            let newFunRule = applySubRule sub'' $ weakenRule {lte = lteSuccRight reflexive} $ applySubRule sub' $ weakenRule {lte = m_lte_m1'} funRule in
            let newArgRule = applySubRule sub'' $ weakenRule {lte = lteSuccRight reflexive} argRule in
            TApp {tyArg = applySub sub'' (weakenTyp (lteSuccRight reflexive) argTy)}
                (rewrite sym prf in newFunRule)
                newArgRule)
