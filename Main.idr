module Main

import Infer
import Lang
import Subst
import Data.Vect
import Data.Vect.Quantifiers
import TypeScope

%default total

main : IO ()
main =
    let Right (_ ** ty ** _) = inferW (Abs $ Abs $ Abs $ App (App (Abs $ Abs $ Var 0) (App (Var 0) (Var 1))) (App (Var 0) (Var 2)))
        | Left _ => pure () in
    printLn ty
