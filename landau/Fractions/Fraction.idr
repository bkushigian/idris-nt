module Fractions.Fraction

import Naturals.PNat

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

theorem39 : x .~ y -> y .~ z -> x .~ z

theorem40 : (x_1, x_2) .~ (x_1 * z, x_2 * z)
