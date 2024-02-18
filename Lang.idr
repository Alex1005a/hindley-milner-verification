module Lang

import Data.Fin
import Data.Vect
import Data.Vect.AtIndex

infixr 2 :->
infix 11 ::>
infix 10 |-

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

    TVar : AtIndex fi env ty ->
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
