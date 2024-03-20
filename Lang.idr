module Lang

import Data.Fin
import Data.Vect
import Data.Vect.AtIndex
import Ext.Basics
import Ext.Nat
import Decidable.Equality

%default total 

infixr 2 :->
infix 11 ::>
infix 10 |-
infix 10 |->
infix 10 |->*

public export
data Term : Nat -> Type where
    Var : Fin n -> Term n
    App : Term n -> Term n -> Term n
    Abs : Term (S n) -> Term n

public export
data Typ
    = TypVar Nat
    | (:->) Typ Typ

export
Show Typ where
    show (TypVar v) = show v
    show (argTy :-> retTy) = "(\{show argTy} -> \{show retTy})"

public export
data TypedTerm : Nat -> Type where
    (::>) : Term n -> Typ -> TypedTerm n

Env = flip Vect Typ

public export
data (|-) : Env n -> TypedTerm n -> Type where

    TVar : {fi : _}
        -> AtIndex fi env ty ->
        ---------------------------
        env |- Var fi ::> ty

    TApp : {argTy : Typ} 
        -> (env |- fun ::> (argTy :-> retTy))
        -> (env |- arg ::> argTy) ->
        ---------------------------
        env |- App fun arg ::> retTy

    TAbs : {argTy : Typ} 
        -> (argTy :: env) |- body ::> retTy ->
        ---------------------------
        env |- Abs body ::> (argTy :-> retTy)

weakenN' : (0 m : Nat) -> Fin n -> Fin (m + n)
weakenN' {n = S k} m FZ = rewrite sym $ plusSuccRightSucc m k in FZ
weakenN' {n = S k} m (FS f) = rewrite sym $ plusSuccRightSucc m k in FS $ weakenN' m f

weakenTerm : Term n -> (l : Nat) -> (k : Nat) -> Term (l + n)
weakenTerm (Var v) w k = ifThenElse (finToNat v < k) (Var (weakenN' w v)) (Var $ shift w v)
weakenTerm (App fun arg) w k = App (weakenTerm fun w k) (weakenTerm arg w k)
weakenTerm (Abs body) w k = let rec = weakenTerm body w (S k) in Abs (rewrite plusSuccRightSucc w n in rec)

substVar : {l : _} -> Fin (l + S n) -> Term n -> Term (l + n)
substVar {l = 0} (FS i) tm = Var i
substVar {l = 0} FZ tm = tm
substVar {l = S l} (FS i) tm = weakenTerm (substVar i tm) 1 0
substVar {l = S l} FZ tm = Var FZ

subst : {l : _} -> Term (l + S n) -> Term n -> Term (l + n)
subst (Var v) tm = substVar v tm
subst (App fun arg) tm = App (subst fun tm) (subst arg tm)
subst (Abs body) tm = Abs $ subst {l = S l} body tm

data Value : Term n -> Type where
    VAbs : Value (Abs body)

data (|->) : Term n -> Term n -> Type where
    RedAppFun : fun |-> rfun
        -> (App fun arg) |-> (App rfun arg)

    RedBeta : (App (Abs body) arg) |-> subst {l = 0} body arg

data (|->*) : Term n -> Term n -> Type where
    RDone : tm |->* tm
    
    RStep : m |->* n
        -> l |-> m
        -> l |->* n

data Progress : Term n -> Type where
  Step : m |-> n
      ----------
    -> Progress m

  Done : Value m
      ----------
    -> Progress m

progress : [] |- (tm ::> ty) -> Progress tm
progress (TAbs body) = Done VAbs
progress (TApp fun arg) =
    case progress fun of
        Done VAbs => Step RedBeta
        Step red => Step $ RedAppFun red

Halts : {n : _} -> Term n -> Typ -> Type
Halts tm ty = (v ** (tm |->* v, Value v))

Reducibility : {n : _} -> Typ -> Env n -> Term n -> Type
Reducibility (TypVar i) env tm = (env |- (tm ::> TypVar i), Halts tm (TypVar i))
Reducibility (argTy :-> retTy) env tm =
    (env |- (tm ::> (argTy :-> retTy)),
        Halts tm (argTy :-> retTy),
        ({tm' : _} -> Reducibility argTy env tm'  -> Reducibility retTy env (App tm tm')))

lemma2 : {ty : _} -> Reducibility ty env tm -> Halts tm ty
lemma2 {ty = TypVar i} (_, h) = h
lemma2 {ty = argTy :-> retTy} (_, h, _) = h

ruleRed : {ty : _} ->  Reducibility ty env tm -> env |- (tm ::> ty)
ruleRed {ty = TypVar i} (rule, _) = rule
ruleRed {ty = argTy :-> retTy} (rule, _) = rule

closedRed : {ty : _} -> env |- (tm ::> ty) ->  Reducibility ty env tm3 -> tm |-> tm3 -> Reducibility ty env tm
closedRed {ty = TypVar i} rr (rule, (v ** (r', norm))) r = (rr, (v ** (RStep r' r, norm)))
closedRed {ty = argTy :-> retTy} rr (rule, (v ** (r', norm)), rfun) r =
    (rr, (v ** (RStep r' r, norm)), \red => closedRed (TApp rr (ruleRed red)) (rfun red) (RedAppFun r))

substAll : {g : _} -> Term (g + n) -> Vect n (Term 0) -> Term g
substAll tm [] = rewrite sym $ plusZeroRightNeutral g in tm
substAll {n = S n} tm (stm :: sub) =
    rewrite sym $ plusZeroRightNeutral g in
    subst {l = g} (substAll (rewrite sym $ plusAssociative g 1 n in tm) sub) stm

substAllBody : (tms : Vect n (Term 0)) -> substAll {g = l} (Abs body) tms === Abs (substAll {g = S l} body tms)
substAllBody [] = rewrite  plusZeroRightNeutral l in Refl
substAllBody {n = S n} (tm :: tms) =
    let rec = substAllBody {l = S l} {body = rewrite plusSuccRightSucc l n in body} tms in
    rewrite sym $ plusSuccRightSucc l n in
    ?substAllBody_rhs

substAllApp : (tms : Vect n (Term 0)) -> substAll {g = l} (App fun arg) tms === App (substAll {g = l} fun tms) (substAll {g = l} arg tms)
substAllApp [] = rewrite plusZeroRightNeutral l in Refl
substAllApp {n = S n} (tm :: tms) = ?substAllApp_rhs -- let rec = substAllApp {arg} {fun} {l = S l} tms in  

weakenVarLTn : {n : _}
    -> {0 t : Typ}
    -> {0 m : _}
    -> {0 pre : Vect n Typ}
    -> {0 env : Vect m Typ}
    -> {0 fi : Fin (n + m)}
    -> (finToNat fi < n) === True
    -> AtIndex fi (pre ++ env) ty
    -> AtIndex (weakenN' 1 fi) (rewrite plusSuccRightSucc n m in pre ++ t :: env) ty
weakenVarLTn {n = S n} {pre = _ :: pre} fi_lt_n Here = rewrite plusSuccRightSucc n m in Here
weakenVarLTn {n = S n} {pre = _ :: pre} fi_lt_n (There later) =
    let rec = weakenVarLTn fi_lt_n later in
    rewrite plusSuccRightSucc n m in
    There (rewrite sym $ plusSuccRightSucc n m in rec)
weakenVarLTn {pre = []} fi_lt_n g =
    let notFalseEqTrue : Not (False === True) = \case Refl impossible in
    let falseEqTrue = trans (sym $ ltZeroFalse $ finToNat fi) fi_lt_n in
    void $ notFalseEqTrue falseEqTrue

weakenVarGTn : {n : _}
    -> {0 t : Typ}
    -> {0 m : _}
    -> {0 pre : Vect n Typ}
    -> {0 env : Vect m Typ}
    -> {0 fi : Fin (n + m)}
    -> (finToNat fi < n) === False
    -> AtIndex fi (pre ++ env) ty
    -> AtIndex (FS fi) (rewrite plusSuccRightSucc n m in pre ++ t :: env) ty
weakenVarGTn {n = S n} {pre = _ :: pre} n_lte_fi (There later) =
    let rec = weakenVarGTn n_lte_fi later in
    rewrite plusSuccRightSucc n m in
    There (rewrite sym $ plusSuccRightSucc n m in rec)
weakenVarGTn {pre = []} n_lte_fi v = There v

weakenRule : {n : _}
    -> {0 m : _} 
    -> {0 pre : Vect n Typ}
    -> {0 env : Vect m Typ}
    -> {0 tm : Term (n + m)}
    -> (pre ++ env) |- (tm ::> ty)
    -> (pre ++ t :: env) |- ((rewrite sym $ plusSuccRightSucc n m in weakenTerm tm 1 n) ::> ty)
weakenRule (TVar {fi} v) =
    rewrite plusSuccRightSucc n m in
    case decEq (finToNat fi < n) True of
        Yes ok =>
            rewrite ok in
            TVar (rewrite sym $ plusSuccRightSucc n m in weakenVarLTn ok v)
        No contra =>
            let ok = notTrueFalse contra in
            rewrite ok in
            TVar (rewrite sym $ plusSuccRightSucc n m in weakenVarGTn ok v)
weakenRule (TAbs {argTy} rbody) =
    let rec = weakenRule {pre = argTy :: pre} rbody in
    rewrite plusSuccRightSucc n m in
    TAbs rec
weakenRule (TApp fun arg) =
    rewrite plusSuccRightSucc n m in
    TApp (weakenRule fun) (weakenRule arg)

substPresVar : {n : _}
    -> {0 m : _} 
    -> {0 arg : Term m}
    -> {0 pre : Vect n Typ} 
    -> {0 env : Vect m Typ} 
    -> {fi : Fin (n + S m)}
    -> env |- (arg ::> ty)
    -> AtIndex fi (pre ++ (ty :: env)) retTy
    -> (pre ++ env) |- (subst {l = n} (Var fi) arg ::> retTy)
substPresVar {pre = _ :: pre} rule Here = TVar Here
substPresVar {pre = _ :: pre} rule (There v) =
    let rec = substPresVar {pre} rule v in
    weakenRule {pre = []} rec
substPresVar {pre = []} rule Here = rule
substPresVar {pre = []} rule (There v) = TVar v

substPresTy : {n : _}
    -> {0 m : _}
    -> {0 tm : Term (n + S m)}
    -> {0 arg : Term m}
    -> {0 pre : Vect n Typ} 
    -> {0 env : Vect m Typ} 
    -> env |- (arg ::> ty)
    -> (pre ++ ty :: env) |- (tm ::> retTy)
    -> (pre ++ env) |- (subst {l = n} tm arg ::> retTy)
substPresTy rule (TVar v) = substPresVar rule v
substPresTy rule (TAbs {argTy} {body} rbody) = TAbs $ substPresTy {pre = argTy :: pre} rule rbody
substPresTy rule (TApp fun arg) = TApp (substPresTy rule fun) (substPresTy rule arg)

appendAssociative : {0 n, m, g : Nat}
    -> (l : Vect n a)
    -> (c : Vect m a)
    -> (r : Vect g a)
    -> l ++ (c ++ r) = (rewrite plusAssociative n m g in (l ++ c) ++ r)
appendAssociative []      c r = Refl
appendAssociative {n = S n} (_::xs) c r =
    rewrite appendAssociative xs c r in
    rewrite sym $ plusAssociative n m g in Refl

appendNilRightNeutral : {0 n : _} -> (l : Vect n a) -> (rewrite sym $ plusZeroRightNeutral n in l ++ []) = l
appendNilRightNeutral []      = Refl
appendNilRightNeutral {n = S n} (_::xs) =
    rewrite appendNilRightNeutral xs in
    rewrite plusZeroRightNeutral n in
    Refl

data EnvTerms : Env n -> Vect n (Term 0) -> Type where
    Nil : EnvTerms [] []
    (::) : Reducibility ty [] tm -> EnvTerms env tms -> EnvTerms (ty :: env) (tm :: tms)

lemma3 : {g : _} -> {env : Env n} -> {tm : Term (g + n)} -> {tms : Vect n (Term 0)} -> {envTms : EnvTerms env tms} -> {pre : Env g}
    -> (pre ++ env) |- (tm ::> ty) -> pre |- (substAll {g} tm tms ::> ty)
lemma3 {n = S n} {env = typ :: env} {envTms = r :: envTms} rule =
    let rec = lemma3 {envTms} {pre = pre ++ [typ]} (rewrite sym $ appendAssociative pre [typ] env in
                                                    rewrite sym $ plusAssociative g 1 n in rule) in
    let srule = substPresTy {pre} (ruleRed r) rec in
    rewrite sym $ appendNilRightNeutral pre in ?lemma3_rhs1
lemma3 {envTms = []} rule = ?lemma3_rhs2

lookupRed : AtIndex fi env ty -> AtIndex fi tms tm -> EnvTerms env tms -> Reducibility ty [] tm
lookupRed Here Here (r :: _) = r
lookupRed (There later) (There later') (_ :: envTms) = lookupRed later later' envTms

fund : {tm, ty : _} -> {env : Env n} -> {tms : Vect n (Term 0)} -> {envTms : EnvTerms env tms}
    -> env |- (tm ::> ty) -> Reducibility ty [] (substAll {g = 0} tm tms)
fund (TVar var) = lookupRed var ?substVarAtIndex envTms
fund (TApp {arg} {fun} fun' arg') =
    let (rule, (v ** (r', norm)), rfun) = fund {envTms} fun' in
    rewrite substAllApp {l = 0} {arg} {fun} tms in
    rfun (fund {envTms} arg')
fund rule@(TAbs {body} rbody) =
    let rule = lemma3 {envTms} {env} rule in
    (rule, (_ ** (rewrite substAllBody {l = 0} {body} tms in RDone, VAbs)), go rule rbody)
    where
    go : {retTy, argTy, tm' : _}
        -> [] |- (substAll (Abs body) tms ::> (argTy :-> retTy))
        -> (argTy :: env) |- (body ::> retTy)
        -> Reducibility argTy [] tm'
        -> Reducibility retTy [] (App (substAll (Abs body) tms) tm')
    go rabs rbody red =
        rewrite substAllBody  {l = 0} {body} tms in
        closedRed {tm = App (Abs (substAll body tms)) tm'}
            (rewrite sym $ substAllBody {l = 0} {body} tms in TApp rabs (ruleRed red)) (fund {envTms = red :: envTms} rbody) RedBeta

weakNorm : {tm, ty : _} -> [] |- (tm ::> ty) -> (v ** (tm |->* v, Value v))
weakNorm rule = lemma2 $ fund {envTms = []} rule

preserve : env |- (tm ::> ty)
  -> tm |-> r
  -> env |- (r ::> ty)
preserve (TApp fun arg) (RedAppFun funRed) = TApp (preserve fun funRed) arg
preserve (TApp (TAbs body) arg) RedBeta = substPresTy {pre = []} arg body

public export
ftv : Typ -> List Nat
ftv (TypVar i) = [i]
ftv (argTy :-> retTy) = ftv argTy ++ ftv retTy

public export
data PartType : Typ -> Nat -> Typ -> Type where
    TyRefl : PartType ty 0 ty
    TyFunArg : PartType ty n argTy -> PartType ty (S n) (argTy :-> retTy)
    TyFunRet : PartType ty n retTy -> PartType ty (S n) (argTy :-> retTy)

argPartType : PartType (argTy :-> retTy) n ty -> PartType argTy (S n) ty
argPartType (TyFunArg partTy) = TyFunArg $ argPartType partTy
argPartType (TyFunRet partTy) = TyFunRet $ argPartType partTy
argPartType TyRefl = TyFunArg TyRefl

retPartType : PartType (argTy :-> retTy) n ty -> PartType retTy (S n) ty
retPartType (TyFunArg partTy) = TyFunArg $ retPartType partTy
retPartType (TyFunRet partTy) = TyFunRet $ retPartType partTy
retPartType TyRefl = TyFunRet TyRefl

export
partTypeSucc : Not (PartType ty (S n) ty)
partTypeSucc (TyFunArg partTy) = partTypeSucc (argPartType partTy)
partTypeSucc (TyFunRet partTy) = partTypeSucc (retPartType partTy)
