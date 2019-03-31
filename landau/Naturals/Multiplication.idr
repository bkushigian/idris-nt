module Naturals.Multiplication

import Logic
import Naturals.PNat
import Naturals.Addition
import Naturals.Order

%access export
%default total

-- Definition 6 (multiplication) can be found in Naturals.PNat as multPNat
-- 2) is defined alternatively as x' * y = y + x * y
theorem28Uniqueness : (x * y = u, x * y = v) -> u = v
theorem28Uniqueness (prf1, prf2) = trans (sym prf1) prf2


-- We need some helpers for theorem29.
-- Both of these seem like they will probably be useful anyways?
multOneLeftIdentity : {x : PNat} -> O * x = x
multOneLeftIdentity {x = O} = Refl
multOneLeftIdentity {x = (N x)} =
    let ih = multOneLeftIdentity {x=x} in
    rewrite ih in
    plusOneRightNext x


multNextLeft : {x, y : PNat} -> (N x) * y = x*y + y
multNextLeft {x} {y = O} = sym (plusOneRightNext x)
multNextLeft {x} {y = (N y)} =
    let ih = multNextLeft {x=x} {y=y} in
    rewrite ih in
    rewrite plusAssociative (x*y) y (N x) in
    rewrite plusAssociative (x*y) x (N y) in
    plusLeft {z=x*y} {x=y+(N x)} {y=x+(N y)} $
    rewrite sym (plusEquivariantRight x y) in
    rewrite sym (plusEquivariantRight y x) in
    cong {f=N} $
    plusCommutative y x

theorem29 : {x : PNat} -> x * y = y * x
theorem29 {x = O} {y} = multOneLeftIdentity
theorem29 {x = (N x)} {y} =
    let ih = theorem29 {x=x} {y=y} in
    let prf2 = plusRight {z=y} ih in
    let prf3 = multNextLeft {x=x} {y=y} in
    prf3 `trans` prf2

multCommutative : {x : PNat} -> x * y = y * x
multCommutative = theorem29


theorem30 : {x : PNat} -> x * (y + z) = (x * y) + (x * z)
theorem30 {x} {y} {z = O} = cong {f= \thing => x * thing} (plusOneRightNext y)
theorem30 {x} {y} {z = (N z)} =
    let ih = theorem30 {x=x} {y=y} {z=z} in
    rewrite sym (plusEquivariantRight y z) in
    rewrite ih in
    rewrite plusAssociative (x*y) (x*z) x in
    Refl

multDistributiveLeft : {x : PNat} -> x * (y + z) = (x * y) + (x * z)
multDistributiveLeft = theorem30

multDistributiveRight : {x : PNat} -> (y + z) * x = (y * x) + (z * x)
multDistributiveRight {x} {y} {z} =
    let com1 = multCommutative {x=y+z} {y=x} in
    let com2 = multCommutative {x=y} {y=x} in
    let com3 = multCommutative {x=z} {y=x} in
    rewrite com1 in
    rewrite com2 in
    rewrite com3 in
    multDistributiveLeft


theorem31 : {x : PNat} -> (x * y) * z = x * (y * z)
theorem31 {x} {y} {z = O} = Refl
theorem31 {x} {y} {z = (N z)} =
    let ih = theorem31 {x=x} {y=y} {z=z} in
    rewrite ih in
    let distr = multDistributiveLeft {x=x} {y=y*z} {z=y} in
    rewrite distr in
    Refl

multAssociative : {x : PNat} -> (x * y) * z = x * (y * z)
multAssociative = theorem31

mutual
    theorem32 : (x .> y -> x*z .> y*z, x = y -> x*z = y*z, x .< y -> x*z .< y*z)
    theorem32 = (_32a, _32b, _32c)

    _32a : x .> y -> x*z .> y*z
    _32a {y} {z} (PlusOnRight {u} x_yu) =
        let prf1 = cong {f = \thing => thing * z} x_yu in
        let prf2 = multDistributiveRight {x=z} {y=y} {z=u} in
        let prf3 = prf1 `trans` prf2 in
        rewrite prf3 in
        theorem18

    _32b : {x : PNat} -> x = y -> x*z = y*z
    _32b Refl = Refl

    _32c : x .< y -> x*z .< y*z
    _32c {z} x_lt_y =
        let y_gt_x = theorem12 x_lt_y in
        let prf1 = _32a {z=z} y_gt_x in
        theorem11 prf1


mutual
    theorem33 : (x*z .> y*z -> x .> y, x*z = y*z -> x = y, x*z .< y*z -> x .< y)
    theorem33 = (_33a, _33b, _33c)

    _33a : x*z .> y*z -> x .> y
    _33a {x} {y} {z = O} xz_gt_yz = xz_gt_yz
    _33a {x} {y} {z = (N zi)} prf =
        let ih = _33a {x=x} {y=y} {z=zi} in
        case theorem10 {x=x} {y=y} of
            (ExactlyOnePf (Left x_y) f) =>
                let prf1 = sym (plusLeft {x=x} {y=y} {z=y*zi} x_y) in
                let prf2 = equalsGreaterThanRight prf prf1 in
                let prf3 = (fst (theorem20 {x=x*zi} {y=y*zi} {z=x})) prf2 in
                let prf4 = ih prf3 in
                prf4
            (ExactlyOnePf (Right (ExactlyOnePf (Left x_gt_y) g)) f) => x_gt_y
            (ExactlyOnePf (Right (ExactlyOnePf (Right x_lt_y) g)) f) =>
                let prf5 = theorem12 x_lt_y in
                let prf6 = (fst (theorem19 {x=y} {y=x} {z=y*zi})) prf5 in
                let prf7 = replace {P = \thing => thing .> x + (y*zi)} (plusCommutative y (y*zi)) prf6 in
                let prf8 = replace {P = \thing => (y*zi)+y .> thing} (plusCommutative x (y*zi)) prf7 in
                let prf9 = prf `greaterThanTransitive` prf8 in
                let prf10 = (fst (theorem20 {x=x*zi} {y=y*zi} {z=x})) prf9 in
                let prf11 = ih prf10 in
                prf11

    _33b : {x : PNat} -> x*z = y*z -> x = y
    _33b {x = O} {y = O} {z} prf = multOneLeftIdentity
    _33b {x = O} {y = (N yi)} {z} prf =
        let prf2 = multNextLeft {x=yi} {y=z} in
        let prf3 = prf `trans` prf2 in
        let prf4 = multOneLeftIdentity {x=z} in
        let prf5 = sym ((sym prf4) `trans` prf3) in
        let contra = theorem7 (yi*z) z in
        void $ contra prf5
    _33b {x = (N xi)} {y = O} {z} prf =
        let prf2 = multNextLeft {x=xi} {y=z} in
        let prf3 = sym prf `trans` prf2 in
        let prf4 = multOneLeftIdentity {x=z} in
        let prf5 = sym ((sym prf4) `trans` prf3) in
        let contra = theorem7 (xi*z) z in
        void $ contra prf5
    _33b {x = (N xi)} {y = (N yi)} {z} prf =
        let prf2 = multNextLeft {x=xi} {y=z} in
        let prf3 = multNextLeft {x=yi} {y=z} in
        let prf4 = sym prf2 `trans` (prf `trans` prf3) in
        let prf5 = plusRightCancel (xi*z) (yi*z) z prf4 in
        let prf6 = _33b {x=xi} {y=yi} {z=z} prf5 in
        cong {f=N} prf6

    _33c : x*z .< y*z -> x .< y
    _33c {x} {y} {z} = theorem11 . (_33a {z=z}) . theorem12

theorem34 : (x .> y, z .> u) -> x*z .> y*u

theorem35 : Either (x .>= y, z .> u) (x .> y, z .>= u) -> x*z .> y*u

theorem36 : (x .>= y, z .>= y) -> x*z .>= y*u
