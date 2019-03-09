module Rats

data Prime : Nat -> Type where
  TwoPrime : Prime 2



||| This represents a simplified rational
data Rat : Nat -> Nat -> Type where
