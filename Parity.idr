module Parity

mutual
  data Even : Nat -> Type where
    ZE : Even Z
    SO : Odd n -> Even (S n)

  data Odd : Nat -> Type where
    SE : Even n -> Odd (S n)

%name Even e
%name Odd  o


total
oddPlusOddEven : Odd n -> Odd m -> Even (n + m)
oddPlusOddEven (SE ZE) (SE x) = SO (SE x)
oddPlusOddEven (SE (SO o)) (SE x) = SO (SE (oddPlusOddEven o (SE x)))

-- oddPlusOddEven (SE ZE) (SE x) = SO (SE x)
-- oddPlusOddEven (SE (SO od)) (SE x) = SO (SE (oddPlusOddEven od (SE x)))

total
oddPlusEvenOdd : Odd n -> Even m -> Odd (n + m)
oddPlusEvenOdd {n} od ZE = rewrite plusZeroRightNeutral n in od
oddPlusEvenOdd (SE ZE) e@(SO o) = SE e
oddPlusEvenOdd (SE (SO o1)) (SO o2) = SE (SO (oddPlusEvenOdd o1 (SO o2)))

total
evenPlusOddOdd : Even n -> Odd m -> Odd (n + m)
evenPlusOddOdd ZE o = o
evenPlusOddOdd (SO (SE e1)) (SE e2) = SE (SO (evenPlusOddOdd e1 (SE e2)))

total
evenPlusEvenEven : Even n -> Even m -> Even (n + m)
evenPlusEvenEven ZE e1 = e1
evenPlusEvenEven {n} od ZE = rewrite plusZeroRightNeutral n in od
evenPlusEvenEven (SO (SE e1)) e2 = SO (SE (evenPlusEvenEven e1 e2))

total
predOddEven : Odd (S n) -> Even n
predOddEven (SE e) = e

total
predNonZeroEvenOdd : Even (S n) -> Odd n
predNonZeroEvenOdd (SO o) = o

