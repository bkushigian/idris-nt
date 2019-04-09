module Fractions.Fraction

import Naturals.PNat
import Naturals.Multiplication

%access public export
%default total

||| Definition 7, fraction x_1 / x_2, stored as (x_1, x_2)
Fraction : Type
Fraction = (PNat, PNat)

top : Fraction -> PNat
top = fst

bot : Fraction -> PNat
bot = snd

infixl 5 .~

||| Definition 8, x_1 / x_2 ~ y_1 / y_2 if x_1*y_2 = y_1*x_2. Unfortu
data (.~) : (lhs : Fraction) -> (rhs : Fraction) -> Type where
    EquivalentCrossMultiply : (top lhs)*(bot rhs) = (top rhs)*(bot lhs) -> lhs .~ rhs

theorem37 : x .~ x
theorem37 = EquivalentCrossMultiply Refl

equalsImpliesEquivalent : x = y -> x .~ y
equalsImpliesEquivalent Refl = theorem37

theorem38 : x .~ y -> y .~ x
theorem38 (EquivalentCrossMultiply prf) = EquivalentCrossMultiply (sym prf)


-- Helper for theorem39
_termRearrange : {x, y, z, u : PNat} -> (x*y) * (z*u) = (x*u) * (z*y)
_termRearrange {x} {y} {z} {u} =
    let r1 = multCommutative {x=z} {y=y} in
    rewrite r1 in
    let r2 = sym (multAssociative {x=x*u} {y=y} {z=z}) in
    rewrite r2 in
    let r3 = multAssociative {x=x} {y=u} {z=y} in
    rewrite r3 in
    let r4 = multCommutative {x=u} {y=y} in
    rewrite r4 in
    let r5 = sym (multAssociative {x=x} {y=y} {z=u}) in
    rewrite r5 in
    let r6 = multAssociative {x=x*y} {y=u} {z=z} in
    rewrite r6 in
    let r7 = multCommutative {x=u} {y=z} in
    rewrite r7 in
    Refl


theorem39 : x .~ y -> y .~ z -> x .~ z
theorem39 (EquivalentCrossMultiply x_y) (EquivalentCrossMultiply y_z) = EquivalentCrossMultiply $
    let prf1 = multiplyEquations x_y y_z in
    let prf2 = _termRearrange {x=(fst x)} {y=(snd y)} {z=(fst y)} {u=(snd z)} in
    let prf3 = _termRearrange {x=(fst y)} {y=(snd x)} {z=(fst z)} {u=(snd y)} in
    let prf4 = prf3 `trans` multCommutative {x=(fst y)*(snd y)} {y=(fst z)*(snd x)} in
    let prf5 = ((sym prf2) `trans` prf1) `trans` prf4 in
    let prf6 = multRightCancel {x=(fst x)*(snd z)} {y=(fst z)*(snd x)} {z=(fst y)*(snd y)} prf5 in
    prf6

theorem40 : {x1, x2, z : PNat} -> (x1, x2) .~ (x1 * z, x2 * z)
theorem40 {x1} {x2} {z} = EquivalentCrossMultiply $
    let r1 = multCommutative {x=x2} {y=z} in
    rewrite r1 in
    sym (multAssociative {x=x1} {y=z} {z=x2})
