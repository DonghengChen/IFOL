import CLM.encode_ts

open IFOL
open encodable
open fin



private def construct:= ℕ ⊕ ℕ ⊕ Fin 7

local notation "cts" v => Sum.inl v
local notation "cr" v => Sum.inr (Sum.inl v)
local notation "catom" => Sum.inr (Sum.inr 0)
local notation "cand" => Sum.inr (Sum.inr 1)
local notation "cor" => Sum.inr (Sum.inr 2)
local notation "cnot" => Sum.inr (Sum.inr 3)
local notation "cimplies" => Sum.inr (Sum.inr 4)
local notation "cforall" => Sum.inr (Sum.inr 5)
local notation "cexists" => Sum.inr (Sum.inr 6)


private def arity: construct → Nat
| cts _ => 0
| cr _ => 0
| catom => 2
| cand => 2
| cor => 2
| cnot => 1
| cimplies => 2
| cforall => 1
| cexists => 1

#check Encodable.encode

def f {σ : Signature}:  Formula σ → Wfin arity:=
  fun form =>by
    cases form with
    | atomic_formula r ts => exact ⟨catom,mk_fn2 (Encodable.encode r) (gpar (σ.arity' r) ts)⟩
    | conjunction f1 f2 => exact ⟨cand, mk_fn2 (f f1) (f f2)⟩
    | disjunction f1 f2 => exact ⟨cor, mk_fn2 (f f1) (f f2)⟩
    | implication f1 f2 => exact ⟨cimpl, mk_fn2 (f f1) (f f2)⟩
    | bottom => exact ⟨cbot,mk_fn0⟩
    | negation f1 => exact ⟨cneg,mk_fn1 (f f1)⟩
    | existential_quantification f1 => exact ⟨cexists,mk_fn1 (f f1)⟩
    | universal_quantification f1 => exact ⟨cforall,mk_fn1 (f f1)⟩
