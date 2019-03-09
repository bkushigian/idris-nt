module NumberTheory

plusMonotonic : LTE a b -> LTE b c -> LTE a c
plusMonotonic LTEZero LTEZero = LTEZero
plusMonotonic LTEZero (LTESucc x) = LTEZero
plusMonotonic (LTESucc x) (LTESucc y) = LTESucc (plusMonotonic x y)

plusStrict

||| A proof that d divides n, given by providing a k
||| such that n = d * k
data Divides : (d : Nat) -> (n : Nat) -> Type where
  Div : (d : Nat) -> (k : Nat) -> Divides d (d * k)

||| A proof that d doesn't divide n
data NDivides : (d : Nat) -> (n : Nat) -> Type where
  NDiv : (Divides d n -> Void) -> NDivides d n

||| Prove that 1 divides everything
oneDividesN : (n : Nat) -> Divides (S Z) n
oneDividesN n = ?myFunc (Div (S Z) n)


data Prime : Nat -> Type where
  P2 : Prime 2
