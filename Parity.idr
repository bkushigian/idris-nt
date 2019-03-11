module Parity

%access public export
%default total

mutual
  data Even : Nat -> Type where
    ZE : Even Z
    SO : Odd n -> Even (S n)

  data Odd : Nat -> Type where
    SE : Even n -> Odd (S n)


data Parity : Nat -> Type where
  ParOdd  : Odd n  -> Parity n
  ParEven : Even n -> Parity n

%name Even e
%name Odd  o
%name Parity p

oddPlusOddEven : Odd n -> Odd m -> Even (n + m)
oddPlusOddEven (SE ZE) (SE x) = SO (SE x)
oddPlusOddEven (SE (SO o)) (SE x) = SO (SE (oddPlusOddEven o (SE x)))

-- oddPlusOddEven (SE ZE) (SE x) = SO (SE x)
-- oddPlusOddEven (SE (SO od)) (SE x) = SO (SE (oddPlusOddEven od (SE x)))

oddPlusEvenOdd : Odd n -> Even m -> Odd (n + m)
oddPlusEvenOdd {n} od ZE = rewrite plusZeroRightNeutral n in od
oddPlusEvenOdd (SE ZE) e@(SO o) = SE e
oddPlusEvenOdd (SE (SO o1)) (SO o2) = SE (SO (oddPlusEvenOdd o1 (SO o2)))

evenPlusOddOdd : Even n -> Odd m -> Odd (n + m)
evenPlusOddOdd ZE o = o
evenPlusOddOdd (SO (SE e1)) (SE e2) = SE (SO (evenPlusOddOdd e1 (SE e2)))

evenPlusEvenEven : Even n -> Even m -> Even (n + m)
evenPlusEvenEven ZE e1 = e1
evenPlusEvenEven {n} od ZE = rewrite plusZeroRightNeutral n in od
evenPlusEvenEven (SO (SE e1)) e2 = SO (SE (evenPlusEvenEven e1 e2))

predOddEven : Odd (S n) -> Even n
predOddEven (SE e) = e

predNonZeroEvenOdd : Even (S n) -> Odd n
predNonZeroEvenOdd (SO o) = o

oneNotEven : Even (S Z) -> Void
oneNotEven (SO (SE _)) impossible

oddNotEven : {x:Nat} -> Odd x -> Even x -> Void
oddNotEven (SE ZE) (SO (SE _)) impossible
oddNotEven (SE (SO o)) (SO (SE e)) = oddNotEven o e

evenNotOdd : {x:Nat} -> Even x -> Odd x -> Void
evenNotOdd e o = oddNotEven o e

getParity : (n : Nat) -> Parity n
getParity Z = ParEven ZE
getParity (S k) = case getParity k of
                       (ParOdd o) => ParEven (SO o)
                       (ParEven e) => ParOdd (SE e)

evenOrOdd : {x : Nat} -> (Even x -> Void) -> (Odd x -> Void) -> Void
evenOrOdd {x} evenContra oddContra = (case getParity x of
          (ParOdd o) => oddContra o
          (ParEven e) => evenContra e)

