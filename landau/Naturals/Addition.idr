||| Proofs from Landau's "Foundations of Analysis", this builds up analysis
||| axiomatically starting at "Naturals" (here, Landau starts at one instead of
||| zero, so we have to define PNat, the type of positive natural numbers).
module Naturals.Addition

import Logic
import Naturals.PNat

%access export
%default total

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

||| If x != y then x' != y'
theorem1 : (x : PNat) -> (y : PNat) -> Not (x = y) -> Not (N x = N y)
theorem1 x y contra prf = contra (axiom4 x y prf)

||| For any natural x, x' != x
theorem2 : (x : PNat) -> Not (N x = x)
theorem2 _ Refl impossible

theorem3 : (x : PNat) -> Not (x = O) -> (u ** x = N u)
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

private thm6Helper : (x : PNat) -> (y : PNat) -> x + N y = N (x + y)
thm6Helper x y = rewrite plusEquivariantRight x y in Refl

theorem6 : (x : PNat) -> (y : PNat) -> x + y = y + x
theorem6 O y = rewrite plusOneRightNext y in Refl
theorem6 (N i) y = let inductiveHypothesis = theorem6 i y in
                       rewrite inductiveHypothesis in
                       rewrite thm6Helper y i in Refl

plusCommutative : (x : PNat) -> (y : PNat) -> x + y = y + x
plusCommutative = theorem6

private thm7Helper : (x : PNat) -> (y : PNat) -> x + (N y) = N y -> x + y = y
thm7Helper x y prf = axiom4 (x + y) y $ replace prf $ plusEquivariantRight x y

theorem7 : (x : PNat) -> (y : PNat) -> Not (x + y = y)
theorem7 O _ Refl impossible
theorem7 (N _) O Refl impossible
theorem7 x (N j) prf = let inductiveHypothesis = theorem7 x j in
                               inductiveHypothesis $ thm7Helper x j prf

theorem8 : (x, y, z : PNat) -> Not (y = z) -> Not (x + y = x + z)
theorem8 O y z contra prf =  contra $ axiom4 y z prf
theorem8 (N j) y z contra prf = let inductiveHypothesis = theorem8 j y z contra in
                          let prf3 = axiom4 (j + y) (j + z) prf in
                                   inductiveHypothesis prf3

-- Helper thing for stuff in Order.idr

OnotPlus : Not (O = x + y)
OnotPlus {x = O} {y = y} = OnotN
OnotPlus {x = x} {y = O} =
   rewrite plusCommutative x O in
   OnotN
OnotPlus {x = (N i)} {y = (N j)} = OnotN
{-
  Theorem 9: For given x and y, exactly one of the following must be the case:
      1) x = y
      2) There exists a u such that x = y + u
      3) There exists a v such that y = x + v

  We break theorem 9 up into a number of subparts.

-}

mutual
  export
  theorem9 : (x, y : PNat) -> ExactlyOne (x = y)
                                         (ExactlyOne (Exists (\v => x = y + v))
                                                     (Exists (\u => x + u = y)))
  theorem9 x y = ExactlyOnePf (theorem9Part1 x y) (theorem9Part2 x y)

  ||| A helper datatype, this allows us to match on the ordering
  private data Order : (x, y : PNat) -> Type where
    Equal : x = y -> Order x y
    Less : (u : PNat) -> x + u = y -> Order x y
    Greater : (v : PNat) -> x = y + v -> Order x y

  ||| Part 1: Prove that at least one of
  |||
  |||       x = y
  |||  and
  |||       ExactlyOne (x = y + v) (x + u = y)
  |||
  ||| This is a lower bound on our statement... we still need to prove that at
  ||| most one of these things is true
  private theorem9Part1 : (x, y : PNat)
               -> Either (x = y) (ExactlyOne (Exists (\v => x = y + v)) (Exists (\u => x + u = y)))
  theorem9Part1 x y = case getOrder x y of
    Equal prf => Left prf
    Less u prf => Right $ ExactlyOnePf (Right (Evidence u prf)) (plusRightImpliesNotPlusLeft x y)
    Greater u prf => Right $ ExactlyOnePf (Left (Evidence u prf)) (plusRightImpliesNotPlusLeft x y)

  ||| Part 2: Prove that at most one of:
  |||
  |||       x = y
  |||  and
  |||       ExactlyOne (x = y + v) (x + u = y)
  |||
  ||| This is an upper bound on our statement.
  private theorem9Part2 : (x, y : PNat)
               -> x = y
               -> Not (ExactlyOne (Exists (\v => x = y + v)) (Exists (\u => x + u = y)))
  theorem9Part2 x y prf1 prfExactlyOne =
    case getWitness prfExactlyOne of
      Left prfExists => case prfExists of
        Evidence v prf2 => equalsImpliesNotPlusRight {x} {y} prf1 v prf2
      Right prfExists => case prfExists of
        Evidence u prf2 => equalsImpliesNotPlusLeft x y prf1 u prf2

  private
  equalsImpliesNotPlusRight : {x, y : PNat} -> x = y -> (v : PNat) -> Not (x = y + v)
  equalsImpliesNotPlusRight {x = y} {y = y} Refl v prf1 =
    theorem7 v y (rewrite plusCommutative v y in rewrite prf1 in Refl)

  private
  equalsImpliesNotPlusLeft : (x, y : PNat) -> x = y -> (u : PNat) -> Not (x + u = y)
  equalsImpliesNotPlusLeft y y Refl u prf1 =
    equalsImpliesNotPlusRight {x=y} {y=y} Refl u (rewrite prf1 in Refl)

  private
  addXToBothSides : (x, y, z : PNat) -> y = z -> x + y = x + z
  addXToBothSides x y z prf = cong prf

  private
  transL : a = b -> a = c -> c = b
  transL prf1 prf2 = trans (sym prf2) prf1

  private
  plusRightImpliesNotPlusLeft : (x, y : PNat) -> Exists (\v => x = y + v) ->
                                                 Exists (\u => x + u = y) -> Void
  plusRightImpliesNotPlusLeft x y prfEx1 prfEx2 = case (prfEx1, prfEx2) of
    (Evidence v prf1, Evidence u prf2) =>
      let prf3 : (u + x = u + (y + v)) = addXToBothSides u x (y + v) prf1 in
      let prf4 : (x + u = u + (y + v)) = transL prf3 $ plusCommutative u x in
      let prf5 : (u + (y + v) = y) = transL prf2 prf4 in
      let prf6 : ((y + v) + u = y) = transL prf5 $ plusCommutative u (y + v) in
      let prf7 : (y + (v + u) = y) = transL prf6 $ plusAssociative y v u in
      let prf8 : ((v + u) + y = y) = transL prf7 $ plusCommutative y (v + u) in
      theorem7 (v + u) y prf8

  ||| Given PNats x and y, determine if x < y, x = y, or x > y
  private getOrder : (x, y : PNat) -> Order x y
  getOrder O O = Equal Refl
  getOrder O (N v) =
    let p : (O + v = N v) = Refl in
    Less v p
  getOrder (N u) O =
    let p : (N u = O + u) = Refl in
    Greater u p
  getOrder (N x) (N y) = case getOrder x y of
    Equal p     => Equal $ cong p
    Less v p    => Less v $ cong p
    Greater u p => Greater u $ cong p
