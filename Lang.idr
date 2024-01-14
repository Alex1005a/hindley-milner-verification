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

    TApp : (env |- fun ::> (argTy :-> retTy))
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
