||| Chapter 1, Section 2 of Landau, on orderings of naturals
module PNatOrder

import PNat
import Landau

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

data (.>) : PNat -> PNat -> Type where
  PlusOnRight : x = y + u -> x .> y

data (.<) : PNat -> PNat -> Type where
  PlusOnLeft : x + v = y -> x .< y


def2 : x = y + u -> x .> y
def2 prf = PlusOnRight prf

def3 : y = x + v -> x .< y
def3 prf = PlusOnLeft (sym prf)

||| For any given x, y, we have exactly one of the cases: x == y, x > y, x < y
theorem10: (x, y : PNat) -> ?abc

MinBound PNat where
  minBound = O

