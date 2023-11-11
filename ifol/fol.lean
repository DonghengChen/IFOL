import Mathlib.Init.Set

structure Signature where
  (function_symbols : Type)
  (relation_symbols : Type)
  (arity : function_symbols → Nat)
  (arity' : relation_symbols → Nat)




inductive term (σ : Signature): Type
| free_variable : Nat → term σ 
| function_application (f : σ.function_symbols) : (Fin (σ.arity f) → term σ ) → term σ 
-- | relation_application (r : σ.relation_symbols) : (Fin (σ.arity' r) → term σ )

inductive formula (σ : Signature) : Type
| atomic_formula : (r : σ.relation_symbols) → (Fin (σ.arity' r) → term σ ) → formula σ
| equalities : term σ → term σ → formula σ
| conjunction : formula σ → formula σ → formula σ
| disjunction : formula σ → formula σ → formula σ
| existential_quantification : Nat → formula σ → formula σ
| universal_quantification : Nat → formula σ → formula σ
| implication : formula σ → formula σ → formula σ
| bottom : formula σ


-- variable {σ : Signature}
-- #check set (formula σ) 

inductive proof (σ : Signature): Set (formula σ) → formula σ → Type
