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

transform_gt : x .> y -> Exists (\v => x = y + v)
transform_gt {x = x} {y = y} (PlusOnRight {u} prf) = Evidence u prf

transform_lt : x .< y -> Exists (\u => x + u = y)
transform_lt {x = x} {y = y} (PlusOnLeft {v} prf) = Evidence v prf

orderEquivGT : Iff (x .> y) (Exists (\v => x = y + v))
orderEquivGT = IffPf transform_gt (
  \exGT => case exGT of
    Evidence v prf => def2 prf
)

orderEquivLT : Iff (x .< y) (Exists (\u => x + u = y))
orderEquivLT = IffPf transform_lt (
  \exLT => case exLT of
     Evidence u prf => def3 $ sym prf
)

mutual
    ||| For any given x, y, we have exactly one of the cases: x == y, x > y, x < y
    theorem10 : ExactlyOne (x = y) (ExactlyOne (x .> y) (x .< y))
    theorem10 {x} {y} = ExactlyOneREquiv (theorem9 x y) outerOrderEquiv

    outerOrderEquiv : Iff (ExactlyOne (Exists (\v => x = y + v)) (Exists (\u => x + u = y)))
                          (ExactlyOne (x .> y) (x .< y))
    outerOrderEquiv = IffPf (\one =>
      let one = ExactlyOneLEquiv one $ Iff.sym orderEquivGT in
        ExactlyOneREquiv one $ Iff.sym orderEquivLT
    )                       (\one =>
      let one = ExactlyOneLEquiv one orderEquivGT in
      ExactlyOneREquiv one orderEquivLT
    )

theorem11 : x .> y -> y .< x
theorem11 (PlusOnRight prf) = PlusOnLeft (sym prf)

theorem12 : x .< y -> y .> x
theorem12 (PlusOnLeft prf) = PlusOnRight (sym prf)

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
theorem13 (PlusOnRight prf) = PlusOnLeft (sym prf)

theorem14 : x .<= y -> y .>= x
theorem14 (PlusOnLeft prf) = PlusOnRight (sym prf)

theorem15 : x .< y -> y .< z -> x .< z
theorem15 (PlusOnLeft {v=xy_v} prf_xy) (PlusOnLeft {v=yz_v} prf_yz) =
    rewrite sym prf_yz in
    rewrite sym prf_xy in
    PlusOnLeft {v=xy_v + yz_v} (sym $ plusAssociative x xy_v yz_v)

lessThanTransitive : x .< y -> y .< z -> x .< z
lessThanTransitive = theorem15

||| This is the preliminary remark given after Theorem 15, since Idris
||| doesn't have the luxury of "simply reading the formula backwards".
greatherThanTransitive : x .> y -> y .> z -> x .> z
greatherThanTransitive xy yz =
    theorem12 $
    lessThanTransitive (theorem11 yz) (theorem11 xy)


notDense : (x : PNat) -> (middle : PNat) -> (x .< middle) -> (middle .< N x) -> Void
notDense x m (PlusOnLeft {v=u} x_u_m) (PlusOnLeft {v=v} m_v_y) =
    let prf3 = replace {P = \mm => mm + v = N x} (sym x_u_m) m_v_y in
    let prf4 = replace (sym (plusOneRightNext x)) prf3 in
    let assoc = plusAssociative x u v in
    let prf5 = trans (sym assoc) (prf4) in
    let prf6 = theorem8 x (u+v) O in
    prf6 (OnotPlus . sym) prf5


greaterThanNotLTE : x .> y -> Not (x .<= y)
greaterThanNotLTE {x = O} {y = y} (PlusOnRight prf) = void $ OnotPlus prf
greaterThanNotLTE {x = (N i)} {y = y} ni_gt_y = \ni_leq_y =>
    notDense y (N i) (theorem11 ni_gt_y) ni_leq_y


notEqLTE : Not (x = y) -> x .<= y -> x .< y
notEqLTE {x} {y} x_neq_y x_lte_y =
    case theorem10 {x=x} {y=y} of
        (ExactlyOnePf (Left x_eq_y) f) => void $ x_neq_y x_eq_y
        (ExactlyOnePf (Right (ExactlyOnePf (Left x_gt_y) g)) f) => void $ (greaterThanNotLTE x_gt_y) x_lte_y
        (ExactlyOnePf (Right (ExactlyOnePf (Right x_lt_y) g)) f) => x_lt_y

theorem16 : Either (x .<= y, y .< z) (x .< y, y .<= z) -> x .< z
theorem16 {x} {y} (Left (x_lte_y, y_lt_z)) = case decEq x y of
    (Yes Refl) => y_lt_z
    (No x_neq_y) => lessThanTransitive (notEqLTE x_neq_y x_lte_y) y_lt_z
theorem16 {y} {z} (Right (x_lt_y, y_lte_z)) = case decEq y z of
    (Yes Refl) => x_lt_y
    (No y_neq_z) => lessThanTransitive x_lt_y (notEqLTE y_neq_z y_lte_z)

theorem17 : x .<= y -> y .<= z -> x .<= z

theorem18 : x + y .> x
theorem18 {x} {y} = PlusOnRight {x=(x + y)} {y=x} {u=y} Refl

mutual
    theorem19 : (x .> y -> x + z .> y + z, x = y -> x + z = y + z, x .< y -> x + z .< y + z)
    theorem19 = (_19a, _19b, _19c)

    _19a : x .> y -> x + z .> y + z

    -- Have to give a type hint here with {x : PNat}
    _19b : {x : PNat} -> x = y -> x + z = y + z

    _19c : x .< y -> x + z .< y + z

mutual
    theorem20 : (x + z .> y + z -> x .> y, x + z = y + z -> x = y, x + z .< y + z -> x .< y)
    theorem20 = (_20a, _20b, _20c)

    _20a : x + z .> y + z -> x .> y

    -- Have to give a type hint here with {x : PNat}
    _20b : {x : PNat} -> x + z = y + z -> x = y

    _20c : x + z .< y + z -> x .< y

theorem21 : x .> y -> z .> u -> x + z .> y + u

theorem22 : Either (x .>= y, z .> u) (x .> y, z .> u) -> x + z .> y + u

theorem23 : x .>= y -> z .>= u -> x + z .>= y + u

theorem24 : x .>= 1

theorem25 : y .> x -> y .>= x + 1

theorem26 : y .< x + y -> y .<= x

MinBound PNat where
  minBound = O
