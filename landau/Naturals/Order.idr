||| Chapter 1, Section 2 of Landau, on orderings of naturals
module Naturals.Order

import Naturals.PNat
import Naturals.Addition
import Logic

%access public export
%default total

-------------------------------------------------------------------------------
---                 Chapter 1, Section 2: Orderings On PNats                ---
-------------------------------------------------------------------------------

Ord PNat where
  compare O O         = EQ
  compare O (N x)     = LT
  compare (N x) O     = GT
  compare (N x) (N y) = compare x y

infix 6 .<
infix 6 .>

data (.>) : (x : PNat) -> (y : PNat) -> Type where
  PlusOnRight : x = y + u -> x .> y

data (.<) : (x : PNat) -> (y : PNat) -> Type where
  PlusOnLeft : x + v = y -> x .< y

def2 : x = y + u -> x .> y
def2 prf = PlusOnRight prf

def3 : {v : PNat} -> y = x + v -> x .< y
def3 prf = PlusOnLeft (sym prf)

mutual
    ||| For any given x, y, we have exactly one of the cases: x == y, x > y, x < y
    theorem10 : ExactlyOne (x = y) (ExactlyOne (x .> y) (x .< y))
    theorem10 {x} {y} =
      case theorem9 x y of
           ExactlyOnePf (Left eq) f => ExactlyOnePf (Left eq) $ f' eq f
           ExactlyOnePf (Right r) f => ?theorem10_rhs_3


    f' : (eq : x = y)
      -> (x = y -> Not (ExactlyOne (Exists (\v => x = (y + v))) (Exists (\u => (x + u) = y))))
      -> (x = y -> Not (ExactlyOne (x .> y) (x .< y)))  -- Return type
    f' eq f eq2 exactly = case exactly of
                               (ExactlyOnePf (Left  gt) f1) => let exists = transform_gt gt in ?f'_rhs_1
                               (ExactlyOnePf (Right lt) f1) => ?f'_rhs_3

    transform_gt : x .> y -> Exists (\v => x = y + v)
    transform_gt {x = x} {y = y} (PlusOnRight {u} prf) = Evidence u prf

    transform_lt : x .< y -> Exists (\u => x + u = y)
    transform_lt {x = x} {y = y} (PlusOnLeft {v} prf) = Evidence v prf


theorem11 : x .> y -> y .< x

theorem12 : x .< y -> y .> x

infix 6 .>=
infix 6 .<=

||| (Definition 4) This is slightly different than what is presented in Landau.
||| The stated def is:
|||        x >= y means x > y or x = y
||| This is equivalent to S x > y.
(.>=) : PNat -> PNat -> Type
x .>= y = N x .> y

||| (Definition 5) As above, this is slightly different than what is given in
||| Landau.
(.<=) : PNat -> PNat -> Type
x .<= y = x .< N y

theorem13 : x .>= y -> y .<= x

MinBound PNat where
  minBound = O

