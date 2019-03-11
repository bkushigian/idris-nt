module NumberTheory

public export data GCD : Nat -> Nat -> Nat -> Type where
  AllDivZ : (d : Nat) -> GCD 0 d d
  DivSumL : GCD l r d -> GCD (l + r) r d
  DivSumR : GCD l r d -> GCD l (l + r) d

public export data Coprime : (a : Nat) -> (b : Nat) -> Type where
  CoPr : GCD a b 1 -> Coprime a b

public export
data Prime : Nat -> Type where
  P2 : Prime 2

-------------------------------------------------------------------------------
--                                   Parity                                  --
-------------------------------------------------------------------------------
mutual
  public export
  data Even : Nat -> Type where
    ZE : Even Z
    SO : Odd n -> Even (S n)

  public export
  data Odd : Nat -> Type where
    SE : Even n -> Odd (S n)

public export
data Parity : Nat -> Type where
  ParOdd  : Odd n  -> Parity n
  ParEven : Even n -> Parity n

%name Even e
%name Odd  o
%name Parity p

||| Prove that plus is monotonic WRT the LTE relation
public export
transitiveLTE : LTE a b -> LTE b c -> LTE a c
transitiveLTE LTEZero LTEZero = LTEZero
transitiveLTE LTEZero (LTESucc x) = LTEZero
transitiveLTE (LTESucc x) (LTESucc y) = LTESucc (transitiveLTE x y)

||| Prove that plus is monotonic WRT the LTE relation
total public export
plusMonotonic : (c : Nat) -> LTE a b -> LTE (c + a) (c + b)
plusMonotonic Z x = x
plusMonotonic (S k) x = LTESucc (plusMonotonic k x)

total public export
multMonotonic : {a : Nat} -> {b : Nat} -> (c : Nat) -> (LTE a b) -> LTE (a * c) (b * c)
multMonotonic {a} {b} Z x = rewrite multCommutative a 0 in rewrite multCommutative b 0 in LTEZero
multMonotonic (S k) LTEZero = LTEZero
multMonotonic {a=S left} {b=S right} k (LTESucc x) = plusMonotonic k (multMonotonic k x)

-- numAndSuccDontDiv : {d : Nat} -> {k : Nat} -> {n : Nat}
--                  -> LT (d * k) n
--                  -> LT n (d * (S k))
--                  -> Divides k n
--                  -> Void
-- numAndSuccDontDiv {d} {k} {n = (S right)} (LTESucc dkLTn) n_lt_dSk kDn = ?numAndSuccDontDiv_rhs_1

-------------------------------------------------------------------------------
--                                Divisibility                               --
-------------------------------------------------------------------------------
||| A proof that d divides n, given by providing a k such that n = d * k
public export
data Divides : (d : Nat) -> (n : Nat) -> Type where
  Div : (d : Nat) -> (k : Nat) -> Divides d (d * k)

||| A proof that d doesn't divide n
public export
data NDivides : (d : Nat) -> (n : Nat) -> Type where
  NDiv : (Divides d n -> Void) -> NDivides d n

oneDividesN : (n : Nat) -> Divides 1 n
oneDividesN Z = Div 1 Z
oneDividesN (S k) = case oneDividesN k of Div (S Z) k => Div (S Z) (S k)

total
plusSRight : (m : Nat) -> (n : Nat) -> plus m (S n) = S (plus m n)
plusSRight Z n = Refl
plusSRight (S k) n = case plusSRight k n of prf  => cong prf

total
plusReducesS : (m : Nat) -> (n : Nat) -> S (plus m n) = plus m (S n)
plusReducesS Z n = Refl
plusReducesS (S k) n = cong (plusReducesS k n)

total
twoDividesEven : {n : Nat} -> Even n -> Divides 2 n
twoDividesEven ZE = Div 2 0
twoDividesEven {n = (S (S _))} (SO (SE e)) = case twoDividesEven e of
                            (Div _ k) => rewrite plusReducesS k (plus k 0) in Div 2 (S k)

























