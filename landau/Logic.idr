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

public export
contrapositive : (p -> q) -> ((q -> Void) -> (p -> Void))
contrapositive prf = \qImpliesFalse => \p => qImpliesFalse $ prf p

--public export
--doubleNegElim : ((p -> Void) -> Void) -> p
--doubleNegElim = believe_me
