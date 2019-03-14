module Logic

%access public export

using (a : Type, P : a -> Type)

  data ExistsUnique : (P : a -> Type) -> Type where
    EvidenceEq : (x : a) -> (pf : P x) -> ((y : a) -> (pfv : P y) -> x = y) -> ExistsUnique P
    
  namespace ExistsUnique
    getWitness : ExistsUnique {a} P -> a
    getWitness (EvidenceEq x pf pfEq) = x

    getProof : (x : ExistsUnique {a} P) -> P (getWitness x)
    getProof (EvidenceEq x pf pfEq) = pf
    
    --- TODO: Fix
    ---getPfEq : (x : ExistsUnique {a} P) -> ((y : a) -> (pfv : P y) -> x = y)
    ---getPfEq (EvidenceEq x pf pfEq) = pfEq
    

public export
contrapositive : (p -> q) -> ((q -> Void) -> (p -> Void))
contrapositive prf = \qImpliesFalse => \p => qImpliesFalse $ prf p
