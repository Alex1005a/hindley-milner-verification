module Infer

import Lang
import Subst
import Unify
import Ext.List
import Data.Vect
import Data.Vect.AtIndex

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

