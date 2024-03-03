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
infix 10 ~~>

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

data (~~>) : Term n -> Term n -> Type where
    RedAppFun : fun ~~> rfun
        -> (App fun arg) ~~> (App rfun arg)
    
    RedAppArg : Value fun
        -> arg ~~> rarg
        -> (App fun arg) ~~> (App fun rarg)

    RedAbs : Value arg
        -> (App (Abs body) arg) ~~> subst {l = 0} body arg

data Progress : Term n -> Type where
  Step : m ~~> n
      ----------
    -> Progress m

  Done : Value m
      ----------
    -> Progress m

progress : [] |- (tm ::> ty) -> Progress tm
progress (TAbs body) = Done VAbs
progress (TApp fun arg) =
    case progress fun of
        Done VAbs => case progress arg of
                        Done val => Step $ RedAbs val
                        Step red => Step $ RedAppArg VAbs red
        Step red => Step $ RedAppFun red

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

preserve : env |- (tm ::> ty)
  -> tm ~~> r
  -> env |- (r ::> ty)
preserve (TApp fun arg) (RedAppFun funRed) = TApp (preserve fun funRed) arg
preserve (TApp fun arg) (RedAppArg vfun argRed) = TApp fun (preserve arg argRed)
preserve (TApp (TAbs body) arg) (RedAbs varg) = substPresTy {pre = []} arg body

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
