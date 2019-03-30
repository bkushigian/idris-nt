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

    _32b : {x : PNat} -> x = y -> x*z = y*z

    _32c : x .< y -> x*z .< y*z

mutual
    theorem33 : (x*z .> y*z -> x .> y, x*z = y*z -> x = y, x*z .< y*z -> x .< y)
    theorem33 = (_33a, _33b, _33c)

    _33a : x*z .> y*z -> x .> y

    _33b : {x : PNat} -> x*z = y*z -> x = y

    _33c : x*z .< y*z -> x .< y

theorem34 : (x .> y, z .> u) -> x*z .> y*u

theorem35 : Either (x .>= y, z .> u) (x .> y, z .>= u) -> x*z .> y*u

theorem36 : (x .>= y, z .>= y) -> x*z .>= y*u
