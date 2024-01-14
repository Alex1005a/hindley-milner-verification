module Control.WellFounded.Lex

import Control.WellFounded
import Data.Nat

public export
data Lex : (Nat, Nat) -> (Nat, Nat) -> Type where
    Left  : LT x1 x2 -> Lex (x1, y1) (x2, y2)
    Right : LT y1 y2 -> Lex (x, y1) (x, y2)

public export
SizeAccessLex : (Nat, Nat) -> Type
SizeAccessLex = Accessible Lex

export
wellFoundLex : (l : Nat) -> (m : Nat) -> SizeAccessLex (l, m)
wellFoundLex l m = Access $ \_ => xacc (wellFounded l) (wellFounded m)
    where
    xacc : SizeAccessible x -> SizeAccessible y ->
        {pair : (Nat, Nat)} -> Lex pair (x, y) -> SizeAccessLex pair
    xacc (Access rec) acc (Left g_lt_x) = Access $ \_ => xacc (rec _ g_lt_x) (wellFounded _)
    xacc acc (Access rec) (Right g_lt_y) = Access $ \_ => xacc acc (rec _ g_lt_y)
