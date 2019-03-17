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
greaterThanTransitive : x .> y -> y .> z -> x .> z
greaterThanTransitive xy yz =
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

eitherLessOrEqual : x .<= y -> Either (x = y) (x .< y)
eitherLessOrEqual {x} {y} (PlusOnLeft {v = O} prf) =
    let prf2 = plusOneRightNext x in
    let nx_eq_ny = (sym prf2) `trans` prf in
    Left (axiom4 x y nx_eq_ny)
eitherLessOrEqual {x} {y} (PlusOnLeft {v = (N i)} prf) =
    let prf2 = plusEquivariantRight x i in
    let prf3 = prf2 `trans` prf in
    let prf4 = axiom4 (x+i) y prf3 in
    Right (PlusOnLeft prf4)

eitherGreaterOrEqual : x .>= y -> Either (x = y) (x .> y)
eitherGreaterOrEqual x_gt_y =
    case eitherLessOrEqual (theorem13 x_gt_y) of
        (Left y_eq_x) => Left (sym y_eq_x)
        (Right y_lt_x) => Right (theorem12 y_lt_x)

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
    _19a {x} {y} {z} (PlusOnRight {u} prf) =
      let prf1 : (x + z = (y + u) + z) = plusRight {y=(y + u)} prf in
      let prf2 : (x + z = y + (u + z)) = trans prf1 $ plusAssociative y u z in
      let prf3 : (y + (u + z) = y + (z + u)) = plusLeft {x=(u + z)} {y=(z + u)} {z=y} $ plusCommutative u z in
      let prf4 : (x + z = y + (z + u)) = trans prf2 $ prf3 in
      let prf5 : (x + z = (y + z) + u) = trans prf4 $ sym $ plusAssociative y z u in
      PlusOnRight {x=(x + z)} {y=(y + z)} {u=u} prf5

    -- Have to give a type hint here with {x : PNat}
    _19b : {x : PNat} -> x = y -> x + z = y + z
    _19b = plusRight

    _19c : x .< y -> x + z .< y + z
    _19c {x} {y} {z} prf = theorem11 {x=(y + z)} {y=(x + z)} $ _19a $ theorem12 prf

mutual
    theorem20 : (x + z .> y + z -> x .> y, x + z = y + z -> x = y, x + z .< y + z -> x .< y)
    theorem20 = (_20a, _20b, _20c)

    _20a : x + z .> y + z -> x .> y
    _20a {x} {y} {z} (PlusOnRight {u} prf) =
        PlusOnRight {u=u} (
            plusRightCancel x (y + u) z $
            rewrite plusAssociative y u z in
            rewrite plusCommutative u z in
            rewrite sym (plusAssociative y z u) in
            prf
        )


    -- I think this fact belongs more to addition than ordering
    -- so I put the main proof there
    -- Have to give a type hint here with {x : PNat}
    _20b : {x : PNat} -> x + z = y + z -> x = y
    _20b {x} {y} {z} prf = plusRightCancel x y z prf

    _20c : x + z .< y + z -> x .< y
    _20c {x} {y} {z} = theorem11 . (_20a {x=y} {y=x} {z=z}) . theorem12

equalsGreaterThanRight : z .> x -> x = y -> z .> y
equalsGreaterThanRight z_gt_x x_eq_y = rewrite sym x_eq_y in z_gt_x

nextLessThan : x .< N x
nextLessThan {x} = rewrite plusCommutative O x in PlusOnLeft {v=O} Refl

equalsImpliesLTE : x = y -> x .<= y
equalsImpliesLTE Refl = nextLessThan

equalsImpliesGTE : x = y -> x .>= y
equalsImpliesGTE Refl = theorem12 nextLessThan

lessThanImpliesLTE : x .< y -> x .<= y
lessThanImpliesLTE {y} x_lt_y = x_lt_y `lessThanTransitive` (nextLessThan {x=y})

greaterThanImpliesGTE : x .> y -> x .>= y
greaterThanImpliesGTE {x} x_gt_y = (theorem12 (nextLessThan {x=x})) `greaterThanTransitive` x_gt_y


theorem21 : x .> y -> z .> u -> x + z .> y + u
theorem21 {y} {z} {u} x_gt_y z_gt_u =
    let theorem19_z = fst (theorem19 {z=z}) in
    let theorem19_y = fst (theorem19 {z=y}) in
    let xz_gt_yz = theorem19_z x_gt_y in    -- x+z > y+z
    let yz_eq_zy = plusCommutative y z in   -- y+z = z+y
    let zy_gt_uy = theorem19_y z_gt_u in    -- z+y > u+y
    let uy_eq_yu = plusCommutative u y in   -- u+y = y+u
    ((xz_gt_yz `equalsGreaterThanRight` yz_eq_zy) `greaterThanTransitive` zy_gt_uy) `equalsGreaterThanRight` uy_eq_yu

theorem22 : Either (x .>= y, z .> u) (x .> y, z .>= u) -> x + z .> y + u
theorem22 {y} {z} {u} (Left (x_gte_y, z_gt_u)) = case eitherGreaterOrEqual x_gte_y of
    (Left Refl) =>
        let theorem19_1_y = fst (theorem19 {z=y}) in
        let prf2 = theorem19_1_y z_gt_u in
        rewrite plusCommutative y z in
        rewrite plusCommutative y u in
        prf2
    (Right x_gt_y) => theorem21 x_gt_y z_gt_u

theorem22 {u} (Right (x_gt_y, z_gte_u)) = case eitherGreaterOrEqual z_gte_u of
    (Left Refl) =>
        let theorem19_1_u = fst (theorem19 {z=u}) in
        theorem19_1_u x_gt_y
    (Right z_gt_u) => theorem21 x_gt_y z_gt_u

theorem23 : x .>= y -> z .>= u -> x + z .>= y + u
theorem23 {y} {u} x_gte_y z_gte_u = case (eitherGreaterOrEqual x_gte_y, eitherGreaterOrEqual z_gte_u) of
    (Left x_eq_y, Left z_eq_u) =>
        PlusOnRight {u=O} $
        rewrite plusCommutative (y+u) O in
        cong (plusEqualities x_eq_y z_eq_u)
    (Left x_eq_y, Right z_gt_u) =>
        greaterThanImpliesGTE $
        theorem22 (Left (equalsImpliesGTE x_eq_y, z_gt_u))
    (Right x_gt_y, Left z_eq_u) =>
        greaterThanImpliesGTE $
        theorem22 (Right (x_gt_y, equalsImpliesGTE z_eq_u))
    (Right x_gt_y, Right z_gt_u) =>
        greaterThanImpliesGTE $
        theorem21 x_gt_y z_gt_u

theorem24 : x .>= 1

theorem25 : y .> x -> y .>= x + 1
theorem25 {x} {y} (PlusOnRight {u} prf) =
  let prf1 : (N y = (x + u) + 1) = trans (cong prf) (sym (plusOneRightNext (x + u))) in
  let prf2 : (N y = x + (u + 1)) = trans prf1 $ plusAssociative x u 1 in
  let prf3 : (x + (u + 1) = x + (1 + u)) = plusLeft {x=(u + 1)} {y=(1 + u)} {z=x} $ plusCommutative u 1 in
  let prf4 : (N y = x + (1 + u)) = trans prf2 prf3 in
  let prf5 : (N y = (x + 1) + u) = trans prf4 $ sym $ plusAssociative x 1 u in
  PlusOnRight {x=N y} {y=(x + 1)} {u=u} prf5

theorem26 : y .< x + y -> y .<= x

MinBound PNat where
  minBound = O
