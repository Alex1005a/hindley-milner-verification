module Main

import Infer
import Lang
import Subst
import Data.Vect

main : IO ()
main =
    let Just ((_ ** ty ** _), _) = inferW (Abs $ Abs $ Abs $ App (App (Abs $ Abs $ Var 0) (App (Var 0) (Var 1))) (App (Var 0) (Var 2))) [] 0
        | Nothing => pure () in
    printLn ty
