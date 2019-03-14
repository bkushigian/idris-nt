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

data ExclusiveOr : (prop1 : Type) -> (prop2 : Type) -> Type where
  ExclusivePf : Either prop1 prop2 ->
                ((prf1 : prop1) -> ((prf2 : prop2) -> Void)) ->
                ((prf2 : prop2) -> ((prf1 : prop1) -> Void)) ->
                ExclusiveOr prop1 prop2

namespace ExclusiveOr
  getWitness : ExclusiveOr prop1 prop2 -> Either prop1 prop2
  getWitness (ExclusivePf w prf1 prf2) = w

public export
contrapositive : (p -> q) -> ((q -> Void) -> (p -> Void))
contrapositive prf = \qImpliesFalse => \p => qImpliesFalse $ prf p
