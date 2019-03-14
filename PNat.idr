module PNat


%access public export
%default total
||| PNat is a positive natural number (one or greater). The definition is
||| the same as that of Nat.
data PNat : Type where
  ||| One
  O : PNat
  ||| Successor
  N : PNat -> PNat

%name PNat i, j, k, m, n


Eq PNat where
  O == O         = True
  (N l) == (N r) = l == r
  _ == _         = False

||| Defining addition on PNats here to allow us to inherit the Num
||| interface and get some nicer syntax.
plusPNat : (x : PNat) -> (y : PNat) -> PNat
plusPNat O y = N y
plusPNat (N i) y = N (plusPNat i y)

||| Defining multiplication on PNats here to allow us to inherit the Num
||| interface and get some nicer syntax.
multPNat : (x : PNat) -> (y : PNat) -> PNat
multPNat O y = y
multPNat (N i) y = (plusPNat y (multPNat i y))

fromIntegerPNat : Integer -> PNat
fromIntegerPNat 1 = O
fromIntegerPNat x = if x > 1 then N (fromIntegerPNat (assert_smaller x (x - 1)))
                             else O

toIntegerPNat : PNat -> Integer
toIntegerPNat O = 1
toIntegerPNat (N i) = 1 + toIntegerPNat i

Cast PNat Integer where
  cast = toIntegerPNat

Uninhabited (O = N n) where
  uninhabited Refl impossible

Uninhabited (N n = O) where
  uninhabited Refl impossible

Uninhabited (N n = n) where
  uninhabited Refl impossible

Uninhabited (n = N n) where
  uninhabited Refl impossible

Num PNat where
  (+) = plusPNat
  (*) = multPNat
  fromInteger = fromIntegerPNat

Abs PNat where
  abs = id

||| Cast non-positive Integers to one
implementation Cast Integer PNat where
  cast = fromInteger

implementation Cast String PNat where
  cast str = cast (the Integer (cast str))

implementation Cast PNat String where
  cast n = cast (the Integer (cast n))

implementation Show PNat where
  show n = show (the Integer (cast n))
  showPrec d n = show n

isOne : PNat -> Bool
isOne O = True
isOne (N _) = False

isNext : PNat -> Bool
isNext = not . isOne

data IsNext : (n : PNat) -> Type where
  ItIsNext : IsNext (N n)

Uninhabited (IsNext O) where
  uninhabited ItIsNext impossible

||| A decision procedure for `IsNext'
isItNext : (n : PNat) -> Dec (IsNext n)
isItNext O = No absurd
isItNext (N i) = Yes ItIsNext

