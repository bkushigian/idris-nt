||| Proofs from Landau's "Foundations of Analysis", this builds up analysis
||| axiomatically starting at "Naturals" (here, Landau starts at one instead of
||| zero). We define PNat, the positive nat
module Landau

{-
axiom 1: one is a natural number

axiom 2: for each x there exists exactly one natural number, called the
         successor of x, which we denote by N x
-}

-------------------------------------------------------------------------------
---                             Define PNat                                 ---
-------------------------------------------------------------------------------
||| PNat is a positive natural number (one or greater). The definition is
||| the same as that of Nat.
data PNat : Type where
  ||| One
  O : PNat
  ||| Successor
  N : PNat -> PNat

%name PNat i, j, k, m, n

Uninhabited (O = N n) where
  uninhabited Refl impossible

Uninhabited (N n = O) where
  uninhabited Refl impossible

total isOne : PNat -> Bool
isOne O = True
isOne (N _) = False

total isNext : PNat -> Bool
isNext = not . isOne

data IsNext : (n : PNat) -> Type where
  ItIsNext : IsNext (N n)

Uninhabited (IsNext O) where
  uninhabited ItIsNext impossible

||| A decision procedure for `IsNext'
isItNext : (n : PNat) -> Dec (IsNext n)
isItNext O = No absurd
isItNext (N i) = Yes ItIsNext

||| We always have x' != 1
total axiom3 : (x : PNat) -> (N x) = O -> Void
axiom3 _ Refl impossible

||| If x' = y' then x = y
total axiom4 : (x : PNat) -> (y : PNat) -> N x = N y -> x = y
axiom4 y y Refl = Refl

||| If x != y then x' != y'
total theorem1 : (x : PNat) -> (y : PNat) -> (x = y -> Void) -> (N x = N y) -> Void
theorem1 x y contra prf = contra (axiom4 x y prf)

||| For any natural x, x' != x
total theorem2 : (x : PNat) -> (N x = x) -> Void
theorem2 _ Refl impossible

total theorem3 : (x : PNat) -> (x = O -> Void) -> (u ** x = N u)
theorem3 x f = ?theorem3_rhs
