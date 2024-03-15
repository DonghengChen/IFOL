import CLM.encode_ts

open IFOL
open encodable
open fin






private def construct:= (ℕ × ℕ) ⊕ Fin 6

local notation "catom" v=> Sum.inl v
local notation "cand" => (Sum.inr 1)
local notation "cor" => (Sum.inr 2)
local notation "cbot" => (Sum.inr 3)
local notation "cimpl" =>  (Sum.inr 4)
local notation "cforall" => (Sum.inr 5)
local notation "cexists" =>  (Sum.inr 0)



@[simp]
private def arity: construct → Nat
| catom _=> 0
| cbot => 0
| cand => 2
| cor => 2
| cimpl => 2
| cforall => 1
| cexists => 1


@[simp]
def f {σ : Signature}:  Formula σ → Wfin arity
| .atomic_formula r ts =>  ⟨catom (r , Encodable.encode ts), mk_fn0 ⟩
| .conjunction f1 f2 =>  ⟨cand, mk_fn2 (f f1) (f f2)⟩
| .disjunction f1 f2 =>  ⟨cor, mk_fn2 (f f1) (f f2)⟩
| .implication f1 f2 =>  ⟨cimpl, mk_fn2 (f f1) (f f2)⟩
| .existential_quantification f1 =>  ⟨cexists,mk_fn1 (f f1)⟩
| .universal_quantification f1 =>  ⟨cforall,mk_fn1 (f f1)⟩
| .bottom => ⟨cbot, mk_fn0⟩

@[simp]
private def fopt1 {α : Type} (x : Option α)(f:α → α): Option (α) :=
  match x with
  | some x => some (f x)
  | none => none

@[simp]
private def fopt2 {α : Type} (x y : Option α)(f:α → α → α): Option (α) :=
  match x,y with
  | some x, some y => some (f x y)
  | _,_ => none

@[simp]
def finv{σ : Signature}: Wfin arity → Option (Formula σ)
| ⟨catom v,_⟩ =>
  match Encodable.decode v.2 with
  | some n => some (Formula.atomic_formula v.1 n)
  | none => none
| ⟨cand,fn⟩ =>fopt2 (finv (fn ⟨0, by decide⟩))  (finv (fn ⟨1, by decide⟩)) Formula.conjunction
| ⟨cor,fn⟩ =>fopt2 (finv (fn ⟨0, by decide⟩))  (finv (fn ⟨1, by decide⟩)) Formula.disjunction
| ⟨cimpl,fn⟩ =>fopt2 (finv (fn ⟨0, by decide⟩))  (finv (fn ⟨1, by decide⟩)) Formula.implication
| ⟨cexists,fn⟩ =>fopt1 (finv (fn ⟨0, by decide⟩)) Formula.existential_quantification
| ⟨cforall,fn⟩ =>fopt1 (finv (fn ⟨0, by decide⟩)) Formula.universal_quantification
| ⟨cbot,_⟩ => some Formula.bottom

instance {σ : Signature}: Encodable (Formula σ) :=by
  haveI h: Encodable (construct) := by
    unfold construct
    exact inferInstance
  apply Encodable.ofLeftInjection f finv
  intro form
  induction form
  simp [f, finv , fopt2, fopt1, *]
  repeat (unfold f<;>simp [finv, fopt2, fopt1, *])
