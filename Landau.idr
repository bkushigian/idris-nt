||| Proofs from Landau's "Foundations of Analysis", this builds up analysis
||| axiomatically starting at "Naturals" (here, Landau starts at one instead of
||| zero, so we have to define PNat, the type of positive natural numbers).
module Landau

import Logic

%access public export
%default total

-------------------------------------------------------------------------------
---                             Define PNat                                 ---
-------------------------------------------------------------------------------

{-
  Landau starts off with four axioms by which he derives all of his theorems.

  axiom 1: one is a natural number

  axiom 2: for each x there exists exactly one natural number, called the
           successor of x, which we denote by N x

  axiom3: 1 is not the successor of any number

  axiom4: If x' = y' then x = y

  These are all handled by the type-theoretic definition of PNat, but we do
  prove axioms 3 and 4 explicitly.
-}

||| PNat is a positive natural number (one or greater). The definition is
||| the same as that of Nat.
data PNat : Type where
  ||| One
  O : PNat
  ||| Successor
  N : PNat -> PNat

%name PNat i, j, k, m, n


Eq PNat where
  O == O         = True
  (N l) == (N r) = l == r
  _ == _         = False

||| Defining addition on PNats here to allow us to inherit the Num
||| interface and get some nicer syntax.
plusPNat : (x : PNat) -> (y : PNat) -> PNat
plusPNat O y = N y
plusPNat (N i) y = N (plusPNat i y)

||| Defining multiplication on PNats here to allow us to inherit the Num
||| interface and get some nicer syntax.
multPNat : (x : PNat) -> (y : PNat) -> PNat
multPNat O y = y
multPNat (N i) y = (plusPNat y (multPNat i y))

fromIntegerPNat : Integer -> PNat
fromIntegerPNat 1 = O
fromIntegerPNat x = if x > 1 then N (fromIntegerPNat (assert_smaller x (x - 1)))
                             else O

toIntegerPNat : PNat -> Integer
toIntegerPNat O = 1
toIntegerPNat (N i) = 1 + toIntegerPNat i

Cast PNat Integer where
  cast = toIntegerPNat

Uninhabited (O = N n) where
  uninhabited Refl impossible

Uninhabited (N n = O) where
  uninhabited Refl impossible

Num PNat where
  (+) = plusPNat
  (*) = multPNat
  fromInteger = fromIntegerPNat

Abs PNat where
  abs = id

||| Cast non-positive Integers to one
Cast Integer PNat where
  cast = fromInteger

Cast String PNat where
  cast str = cast (the Integer (cast str))

Cast PNat String where
  cast n = cast (the Integer (cast n))

Show PNat where
  show n = show (the Integer (cast n))
  showPrec d n = show n

isOne : PNat -> Bool
isOne O = True
isOne (N _) = False

isNext : PNat -> Bool
isNext = not . isOne

data IsNext : (n : PNat) -> Type where
  ItIsNext : IsNext (N n)

Uninhabited (IsNext O) where
  uninhabited ItIsNext impossible

||| A decision procedure for `IsNext'
isItNext : (n : PNat) -> Dec (IsNext n)
isItNext O = No absurd
isItNext (N i) = Yes ItIsNext

--------------------------------------------------------------------------------
---                               Begin Proofs                               ---
--------------------------------------------------------------------------------

||| We always have x' != 1
axiom3 : (x : PNat) -> (N x) = O -> Void
axiom3 _ Refl impossible

||| If x' = y' then x = y
axiom4 : (x : PNat) -> (y : PNat) -> N x = N y -> x = y
axiom4 y y Refl = Refl

||| If x != y then x' != y'
theorem1 : (x : PNat) -> (y : PNat) -> (x = y -> Void) -> (N x = N y) -> Void
theorem1 x y contra prf = contra (axiom4 x y prf)

||| For any natural x, x' != x
theorem2 : (x : PNat) -> (N x = x) -> Void
theorem2 _ Refl impossible

theorem3 : (x : PNat) -> (x = O -> Void) -> (u ** x = N u)
theorem3 O contra = void (contra Refl)
theorem3 (N i) contra = (i ** Refl)

||| Theorem 4, and definition 1: To every pair of numbers x, y we may assign in
||| exactly one way a natural number, called x + y, such that
|||   1. 1 + y = y'
|||   2. x' + y = (x + y)'
theorem4 : (x, y : PNat) -> ExistsUnique (\a => a = x + y)
theorem4 x y = let u : PNat = x + y in
               let pf : (u = x + y) = Refl in
               let pfEq : ((v : PNat) -> (v = x + y) -> (u = v)) = \v, pfv => trans pf $ sym pfv in
               EvidenceEq u pf pfEq

theorem5 : (x : PNat) -> (y : PNat) -> (z : PNat) -> (x + y) + z = x + (y + z)
theorem5 O y z = Refl
theorem5 (N i) y z = cong (theorem5 i y z)

plusAssociative : (x : PNat) -> (y : PNat) -> (z : PNat)
               -> (x + y) + z = x + (y + z)
plusAssociative = theorem5

plusOneRightNext : (x : PNat) -> x + O = N x
plusOneRightNext O = Refl
plusOneRightNext (N i) = let inductiveHypothesis = plusOneRightNext i in
                             cong inductiveHypothesis 

plusBilinearLeft : (x : PNat) -> (y : PNat) -> N (x + y) = N x + y
plusBilinearLeft O y = Refl
plusBilinearLeft (N i) y = cong $ plusBilinearLeft i y

plusBilinearRight : (x : PNat) -> (y : PNat) -> N (x + y) = x + N y
plusBilinearRight O y = Refl
plusBilinearRight (N i) y = cong $ plusBilinearRight i y

thm6Helper : (x : PNat) -> (y : PNat) -> x + N y = N (x + y)
thm6Helper x y = rewrite plusBilinearRight x y in Refl

theorem6 : (x : PNat) -> (y : PNat) -> x + y = y + x
theorem6 O y = rewrite plusOneRightNext y in Refl
theorem6 (N i) y = let inductiveHypothesis = theorem6 i y in 
                       rewrite inductiveHypothesis in 
                       rewrite thm6Helper y i in Refl

plusCommutative : (x : PNat) -> (y : PNat) -> x + y = y + x
plusCommutative = theorem6

thm7Helper : (x : PNat) -> (y : PNat) -> x + (N y) = N y -> x + y = y
thm7Helper x y prf = axiom4 (x + y) y $ replace prf $ plusBilinearRight x y

theorem7 : (x : PNat) -> (y : PNat) -> x + y = y -> Void
theorem7 O _ Refl impossible
theorem7 (N _) O Refl impossible
theorem7 x (N j) prf = let inductiveHypothesis = theorem7 x j in
                               inductiveHypothesis $ thm7Helper x j prf

theorem8 : (x, y, z : PNat) -> (y = z -> Void) -> x + y = x + z -> Void
theorem8 O y z contra prf =  contra $ axiom4 y z prf
theorem8 (N j) y z contra prf = let inductiveHypothesis = theorem8 j y z contra in
                          let prf3 = axiom4 (j + y) (j + z) prf in
                                   inductiveHypothesis prf3

equalsImpliesNotPlusRight : (x, y : PNat) -> x = y -> (v : PNat) -> x = y + v -> Void

equalsImpliesNotPlusLeft : (x, y : PNat) -> x = y -> (u : PNat) -> x + u = y -> Void

plusLeftImpliesNotEqual : (x, y, u : PNat) -> x + u = y -> x = y -> Void

plusLeftImpliesNotPlusRight : (x, y, u, v: PNat) -> x + u = y -> x = y + v -> Void

plusRightImpliesNotEqual : (x, y, v : PNat) -> x = y + v -> x = y -> Void

plusRightImpliesNotPlusLeft : (x, y, u, v: PNat) -> x = y + v -> x + u = y -> Void

--- TODO: implement `exclusive or` to replace with Either
---theorem9 : (x, y : PNat) -> Either (x = y) (ExistsUnique (\u => Either (x = y + u) (y = x + u)))
---theorem9 x y = if x == y then Left (x == y) else
---               ?hole






-------------------------------------------------------------------------------
---                     Chapter 2: Orderings On PNats                       ---
-------------------------------------------------------------------------------

Ord PNat where
  compare O O         = EQ
  compare O (N x)     = LT
  compare (N x) O     = GT
  compare (N x) (N y) = compare x y

MinBound PNat where
  minBound = O

