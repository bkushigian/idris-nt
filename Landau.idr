||| Proofs from Landau's "Foundations of Analysis", this builds up analysis
||| axiomatically starting at "Naturals" (here, Landau starts at one instead of
||| zero, so we have to define PNat, the type of positive natural numbers).
module Landau

import Logic
import PNat

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

plusEquivariantLeft : (x : PNat) -> (y : PNat) -> N (x + y) = N x + y
plusEquivariantLeft O y = Refl
plusEquivariantLeft (N i) y = cong $ plusEquivariantLeft i y

plusEquivariantRight : (x : PNat) -> (y : PNat) -> N (x + y) = x + N y
plusEquivariantRight O y = Refl
plusEquivariantRight (N i) y = cong $ plusEquivariantRight i y

thm6Helper : (x : PNat) -> (y : PNat) -> x + N y = N (x + y)
thm6Helper x y = rewrite plusEquivariantRight x y in Refl

theorem6 : (x : PNat) -> (y : PNat) -> x + y = y + x
theorem6 O y = rewrite plusOneRightNext y in Refl
theorem6 (N i) y = let inductiveHypothesis = theorem6 i y in 
                       rewrite inductiveHypothesis in 
                       rewrite thm6Helper y i in Refl

plusCommutative : (x : PNat) -> (y : PNat) -> x + y = y + x
plusCommutative = theorem6

thm7Helper : (x : PNat) -> (y : PNat) -> x + (N y) = N y -> x + y = y
thm7Helper x y prf = axiom4 (x + y) y $ replace prf $ plusEquivariantRight x y

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

equalsImpliesNotPlusRight : {x, y : PNat} -> x = y -> (v : PNat) -> x = y + v -> Void
equalsImpliesNotPlusRight {x = y} {y = y} Refl v prf1 = theorem7 v y (rewrite plusCommutative v y in rewrite prf1 in Refl)

addXToBothSides : (x, y, z : PNat) -> y = z -> x + y = x + z
addXToBothSides x y z prf = cong prf

transL : a = b -> a = c -> c = b
transL prf1 prf2 = trans (sym prf2) prf1

equalsImpliesNotPlusLeft : (x, y : PNat) -> x = y -> (u : PNat) -> x + u = y -> Void
equalsImpliesNotPlusLeft y y Refl u prf1 = equalsImpliesNotPlusRight {x=y} {y=y} Refl u (rewrite prf1 in Refl)

plusLeftImpliesNotEqual : (x, y, u : PNat) -> x + u = y -> x = y -> Void
plusLeftImpliesNotEqual x y u prf prf1 = equalsImpliesNotPlusLeft x y prf1 u prf

plusRightImpliesNotEqual : (x, y, v : PNat) -> x = y + v -> x = y -> Void
plusRightImpliesNotEqual x y v prf1 prf2 =
  let prf3 : (y + v = y) = trans (sym prf1) prf2 in
  let prf4 : (v + y = y) = transL prf3 $ plusCommutative y v in
  theorem7 v y prf4

plusRightImpliesNotPlusLeft : (x, y, u, v: PNat) -> x = y + v -> x + u = y -> Void
plusRightImpliesNotPlusLeft x y u v prf1 prf2 =
  let prf3 : (u + x = u + (y + v)) = addXToBothSides u x (y + v) prf1 in
  let prf4 : (x + u = u + (y + v)) = transL prf3 $ plusCommutative u x in
  let prf5 : (u + (y + v) = y) = transL prf2 prf4 in
  let prf6 : ((y + v) + u = y) = transL prf5 $ plusCommutative u (y + v) in
  let prf7 : (y + (v + u) = y) = transL prf6 $ plusAssociative y v u in
  let prf8 : ((v + u) + y = y) = transL prf7 $ plusCommutative y (v + u) in
  theorem7 (v + u) y prf8

--theorem9Part1 : (x, y : PNat) -> Either (x = y) (Exists (\u => ExclusiveOr (x = y + u) (x + u = y)))
--theorem9Part1 x y = if x == y then Left Refl else
--                    Right $ theorem9Part1Part2 x y Refl

--theorem9Part1Part2 : (x, y : PNat) -> x = y -> ((Exists (\u => ExclusiveOr (x = y + u) (x + u = y))) -> Void)
--theorem9Part1Part2 x y prf = \prfEx => case getWitness $ getProof prfEx of
--                                         Left prf => equalsImpliesNotPlusLeft x y u prf
--                                         Right prf => equalsImpliesNotPlusRight x y u prf

--theorem9 : (x, y : PNat) -> ExclusiveOr (x = y) (Exists (\u => ExclusiveOr (x = y + u) (x + u = y)))
--theorem9 x y = ExclusivePf (theorem9Part1 x y) (theorem9Part2 x y) (theorem9Part3 x y)






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

