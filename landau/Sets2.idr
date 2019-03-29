module Sets2

import Naturals.PNat
import Naturals.Order
import Naturals.Addition
import Logic


-- A set of PNats is a family of propositions indexed by PNats
PSet : Type
PSet = PNat -> Type

-- A set of PNats is a decidable set if the proposition for each n is decidable
data SetDec : (s : PSet) -> Type where
    AllDec : ((n : PNat) -> Dec (s n)) -> SetDec s

-- A PNat x is in the set if the proposition (P x) is true (has a proof)
data SetElem : (x : PNat) -> (s : PSet) -> Type where
    Satisfies : (prf : s x) -> SetElem x s

-- We can easily define operations on sets
setIntersection : PSet -> PSet -> PSet
setIntersection u v = \n => (u n, v n)

setUnion : PSet -> PSet -> PSet
setUnion u v = \n => Either (u n) (v n)

setComplement : PSet -> PSet
setComplement u = \n => Not (u n)

-- A set is a subset of another set if the proposition implies the other
data IsSubset : (u : PSet) -> (v : PSet) -> Type where
    ConditionImplies : ((n : PNat) -> u n -> v n) -> IsSubset u v


-- Here is an example of a set, all the PNats that are not equal to O
NotOne : PSet
NotOne = \n => Not (n = O)

-- We prove it is a decidable set
NotOneDec : SetDec NotOne
NotOneDec = AllDec $ \n =>
    case decEq n O of
        (Yes prf) => No (notNot prf)
        (No contra) => Yes contra

-- We can show that O is not an element of it
oneNotElem : Not (O `SetElem` NotOne)
oneNotElem = \elem => case elem of
    (Satisfies prf) => prf Refl

-- And that any n >= 2 is an element
ge2Elem : (x : PNat) -> (x .>= 2) -> x `SetElem` NotOne
ge2Elem (N u) (PlusOnRight Refl) = Satisfies (axiom3 u)


-- A set has been proved to be empty if we can prove the proposition is false for all n
data IsEmpty : (s : PSet) -> Type where
    AllFalse : ((n : PNat) -> Not (n `SetElem` s)) -> IsEmpty s


-- We know a set contains something if there exists an element in the set
data ContainsSomething : (s : PSet) -> Type where
    HasElement : (n ** n `SetElem` s) -> ContainsSomething s


-- Here is another example set: the set for which n is equal to 1 and 2
OneAndTwo : PSet
OneAndTwo = \n => (n = 1, n = 2) -- could also be done with setIntersection

-- We can prove that this set is empty
OneAndTwoEmpty : IsEmpty OneAndTwo
OneAndTwoEmpty = AllFalse $ \n,(Satisfies (prf1, prf2)) => absurd $ (sym prf1) `trans` prf2


-- A set that contains something is NOT the empty set
nonEmpty' : ContainsSomething s -> Not (IsEmpty s)
nonEmpty' {s} (HasElement (x ** pf)) = \empty => case empty of
    (AllFalse f) => f x pf


-- We can show axiom5
axiom5 : (s : PSet) -> O `SetElem` s -> ((x : PNat) -> x `SetElem` s -> (N x) `SetElem` s) -> (y : PNat) -> y `SetElem` s
axiom5 s one_elem next_elem O = one_elem
axiom5 s one_elem next_elem (N i) = next_elem i (axiom5 s one_elem next_elem i)


-- Everything below here is a proof of theorem27 (the main theorem is at the bottom)
-- This is a weaker version of theorem27 presented in the book in two ways:
--  1. The set is required to be decidable,
--  2. and we require ContainsSomething s, not just Not (IsEmpty s)


lte1 : x .<= O -> x = O
lte1 {x = O} x_o = Refl
lte1 {x = (N i)} (PlusOnLeft {v} prf) =
    let contra = axiom4 (i + v) O prf in
    void $ OnotPlus (sym contra)

emptyDecLe : (g : PSet) -> (gDec : SetDec g) -> (x : PNat) -> Either ((y : PNat) -> y .<= x -> Not (y `SetElem` g)) (z : PNat ** (z `SetElem` g, z .<= x))
emptyDecLe g (AllDec decF) O = case decF O of
    (Yes gO) => Right (O ** (Satisfies gO, lessThanNext))
    (No contra) => Left (\y,y_lte_O,(Satisfies gy) =>
        let y_O = lte1 y_lte_O in
        let gnx = replace {P = \thing => g thing} y_O gy in
        contra gnx
    )

emptyDecLe g gDec@(AllDec decF) (N x) = case decF (N x) of
    (Yes gnx) => Right (N x ** (Satisfies gnx, lessThanNext))
    (No contra) =>
        case emptyDecLe g gDec x of
            (Right (z ** prf)) => Right (z ** (fst prf, (snd prf) `lessThanTransitive` lessThanNext))
            (Left allBad) => Left (\y,y_lt_nnx,(Satisfies gy) =>
                case theorem10 {x = y} {y = N x} of
                    (ExactlyOnePf (Left y_nx) f) =>
                        let gnx = replace {P = \thing => g thing} y_nx gy in
                        contra gnx
                    (ExactlyOnePf (Right (ExactlyOnePf (Left y_gt_nx) g)) f) =>
                        notDense (N x) y (theorem11 y_gt_nx) y_lt_nnx
                    (ExactlyOnePf (Right (ExactlyOnePf (Right y_lt_nx) g)) f) =>
                        allBad y y_lt_nx (Satisfies gy)
            )


lessThanN : x .< y -> N x .< N y
lessThanN (PlusOnLeft x_y) = PlusOnLeft (cong x_y)

lessThanN_not : Not (N x .<= N y) -> Not (x .<= y)
lessThanN_not nx_ny_not = \x_y => nx_ny_not (lessThanN x_y)

notLTE : Not (y .<= i) -> i .< y
notLTE {y = O} {i = i} prf = void $ prf (theorem13 theorem24)
notLTE {y = (N yy)} {i = O} prf = theorem13 theorem24
notLTE {y = (N yy)} {i = (N ii)} prf =
    let ih = notLTE (lessThanN_not prf) in
    lessThanN ih


checkEmpty : (g : PSet) -> (gDec : SetDec g) -> (i : PNat) -> (empty : (z : PNat) -> (z .<= i) -> Not (SetElem z g)) -> (y : PNat) -> (y_elem : SetElem y g) -> (N i .< N y)
checkEmpty g gDec i empty y y_elem =
    lessThanN $
    let y_leq_i_not = flip (empty y) y_elem in
    notLTE y_leq_i_not



greaterThanBound : (g : PSet) -> (u : PNat) -> ((y : PNat) -> y .<= u -> Not (y `SetElem` g)) -> (e : PNat) -> e `SetElem` g -> e .> u
greaterThanBound g O imp O e_elem = void $ imp O lessThanNext e_elem
greaterThanBound g O imp (N i) e_elem = theorem24
greaterThanBound g (N i) imp e e_elem = case theorem10 {x=e} {y=N i} of
    (ExactlyOnePf (Left e_ni) f) =>
        void $ imp e (equalsImpliesLTE e_ni) e_elem
    (ExactlyOnePf (Right (ExactlyOnePf (Left l) g)) f) => l
    (ExactlyOnePf (Right (ExactlyOnePf (Right e_lt_ni) g)) f) =>
        let e_lt_nni = e_lt_ni `lessThanTransitive` lessThanNext in
        void $ imp e e_lt_nni e_elem

sandwich : b .< x -> x .< N (N b) -> x = N b
sandwich {b} {x} b_x x_nnb = case eitherLessOrEqual x_nnb of
    (Left eq) => eq
    (Right x_lt_nb) => void $ notDense b x b_x x_lt_nb


theorem27' : (g : PSet) -> (gDec : SetDec g) -> (u : PNat) -> (e : PNat ** (e `SetElem` g, e .<= u)) -> (x : PNat ** (x `SetElem` g, (y : PNat) -> y `SetElem` g -> x .<= y))
theorem27' g gDec O (e ** (e_elem, e_O)) =
    let e_is_O = lte1 e_O in
    let o_elem = replace {P = \thing => SetElem thing g} e_is_O e_elem in
    (O ** (o_elem, \y,_ => theorem13 theorem24))
theorem27' g gDec (N uu) (e ** (e_elem, e_lte)) = case emptyDecLe g gDec uu of
    (Left empty) =>
        let e_gt_u = greaterThanBound g uu empty e e_elem in
        let e_nuu : (e = N uu) = sandwich (theorem11 e_gt_u) e_lte in
        let nuu_elem = replace {P = \thing => thing `SetElem` g} e_nuu e_elem in
        (N uu ** (nuu_elem, \y,y_elem => checkEmpty g gDec uu empty y y_elem))
    (Right zLessExists) => theorem27' g gDec uu zLessExists

theorem27 : (g : PSet) -> (gDec : SetDec g) -> ContainsSomething g -> (x : PNat ** (x `SetElem` g, (y : PNat) -> y `SetElem` g -> x .<= y))
theorem27 g gDec (HasElement (u ** e_elem)) = theorem27' g gDec u (u ** (e_elem, equalsImpliesLTE Refl))
