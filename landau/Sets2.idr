module Sets2

import Naturals.PNat
import Naturals.Order
import Naturals.Addition
import Logic


PSet : Type
PSet = PNat -> Type

data SetDec : (s : PSet) -> Type where
    AllDec : ((n : PNat) -> Dec (s n)) -> SetDec s

data SetElem : (x : PNat) -> (s : PSet) -> Type where
    Satisfies : (prf : s x) -> SetElem x s

setIntersection : PSet -> PSet -> PSet
setIntersection u v = \n => (u n, v n)

setUnion : PSet -> PSet -> PSet
setUnion u v = \n => Either (u n) (v n)

setComplement : PSet -> PSet
setComplement u = \n => Not (u n)

data IsSubset : (u : PSet) -> (v : PSet) -> Type where
    ConditionImplies : ((n : PNat) -> u n -> v n) -> IsSubset u v



NotOne : PSet
NotOne = \n => Not (n = 0)

NotOneDec : SetDec NotOne
NotOneDec = AllDec $ \n =>
    case decEq n 0 of
        (Yes prf) => No (notNot prf)
        (No contra) => Yes contra


oneNotElem : Not (O `SetElem` NotOne)
oneNotElem = \elem => case elem of
    (Satisfies prf) => prf Refl

ge2Elem : (x : PNat) -> (x .>= 2) -> x `SetElem` NotOne
ge2Elem (N u) (PlusOnRight Refl) = Satisfies (axiom3 u)

data IsEmpty : (s : PSet) -> Type where
    AllFalse : ((n : PNat) -> Not (n `SetElem` s)) -> IsEmpty s

data ContainsSomething : (s : PSet) -> Type where
    HasElement : (n ** n `SetElem` s) -> ContainsSomething s

OneAndTwo : PSet
OneAndTwo = \n => (n = 1, n = 2) -- could also be done with setIntersection

OneAndTwoEmpty : IsEmpty OneAndTwo
OneAndTwoEmpty = AllFalse $ \n,(Satisfies (prf1, prf2)) => absurd $ (sym prf1) `trans` prf2


nonEmpty' : ContainsSomething s -> Not (IsEmpty s)
nonEmpty' {s} (HasElement (x ** pf)) = \empty => case empty of
    (AllFalse f) => f x pf

axiom5 : (s : PSet) -> O `SetElem` s -> ((x : PNat) -> x `SetElem` s -> (N x) `SetElem` s) -> (y : PNat) -> y `SetElem` s
axiom5 s one_elem next_elem O = one_elem
axiom5 s one_elem next_elem (N i) = next_elem i (axiom5 s one_elem next_elem i)


-- nonInduction : (s : PSet) -> O `SetElem` s -> (n ** Not (n `SetElem` s)) -> (m ** (m `SetElem` s, Not ((N m) `SetElem` s)))


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

-- containsLessThan

-- lem : (g : PSet) -> (y : PNat) -> y `SetElem` g -> ((x : PNat) -> x .<= N i -> Not (SetElem x g)) ->

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

-- greaterThanBound g u imp O e_elem = void $ imp O (theorem13 theorem24) e_elem
-- greaterThanBound g u imp (N i) e_elem = ?greaterThanBound_rhs_2

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
