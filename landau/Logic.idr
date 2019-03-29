module Logic

%access public export

using (a : Type, P : a -> Type)

  data ExistsUnique : (P : a -> Type) -> Type where
    EvidenceEq : (x : a) -> (pf : P x) -> ((y : a) -> (pfv : P y) -> x = y) -> ExistsUnique P

  namespace ExistsUnique
    getWitness : ExistsUnique {a} P -> a
    getWitness (EvidenceEq x pf pfEq) = x

    getProof : (eu : ExistsUnique {a} P) -> P (getWitness eu)
    getProof (EvidenceEq x pf pfEq) = pf

    getPfEq : (eu : ExistsUnique {a} P) -> ((y : a) -> (pfv : P y) -> getWitness eu = y)
    getPfEq (EvidenceEq x pf pfEq) = pfEq

data ExactlyOne : (prop1 : Type) -> (prop2 : Type) -> Type where
  ExactlyOnePf : Either prop1 prop2 ->
                 ((prf1 : prop1) -> ((prf2 : prop2) -> Void)) ->
                 ExactlyOne prop1 prop2

namespace ExactlyOne
  getWitness : ExactlyOne prop1 prop2 -> Either prop1 prop2
  getWitness (ExactlyOnePf w prf) = w

data Iff : (prop1 : Type) -> (prop2 : Type) -> Type where
  IffPf : (prop1 -> prop2) -> (prop2 -> prop1) -> Iff prop1 prop2

namespace Iff
  sym : Iff prop1 prop2 -> Iff prop2 prop1
  sym (IffPf f g) = IffPf g f

public export
contrapositive : (p -> q) -> ((q -> Void) -> (p -> Void))
contrapositive prf = \qImpliesFalse => \p => qImpliesFalse $ prf p

ExactlyOneREquiv : ExactlyOne prop1 prop2 -> (Iff prop2 prop3) -> ExactlyOne prop1 prop3
ExactlyOneREquiv (ExactlyOnePf (Left w1) contra) (IffPf f g) =
  ExactlyOnePf (Left w1) (\prf1, prf3 => contra prf1 (g prf3))
ExactlyOneREquiv (ExactlyOnePf (Right w2) contra) (IffPf f g) =
  ExactlyOnePf (Right (f w2)) (\prf1, prf3 => contra prf1 (g prf3))

ExactlyOneLEquiv : ExactlyOne prop1 prop2 -> (Iff prop1 prop3) -> ExactlyOne prop3 prop2
ExactlyOneLEquiv (ExactlyOnePf (Left w1) contra) (IffPf f g) =
  ExactlyOnePf (Left (f w1)) (\prf3, prf2 => contra (g prf3) prf2)
ExactlyOneLEquiv (ExactlyOnePf (Right w2) contra) (IffPf f g) =
  ExactlyOnePf (Right w2) (\prf3, prf2 => contra (g prf3) prf2)

--public export
--doubleNegElim : ((p -> Void) -> Void) -> p
--doubleNegElim = believe_me

notNot : a -> Not (Not a)
notNot x = \f => f x
