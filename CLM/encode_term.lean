import CLM.IFOL
import CLM.encodable

open IFOL
open encodable
open fin

private def construct:= ℤ ⊕ ℕ
local notation "cfree" v => Sum.inl v
local notation "cconst" v => Sum.inr v

@[reducible]
private def arity: construct → Nat
| (cfree _) => 0
| (cconst _)  => 0

def g{σ : Signature}: Term σ → Wfin arity:=
fun term => by
cases term with
| free n => let m:= match n with
                    | .free_variable v => v
            exact ⟨cfree m, mk_fn0⟩
| const n =>let m:= match n with
                    | .Constant v => v
            exact ⟨cconst m, mk_fn0⟩

private def decode0(σ : Signature) :Wfin arity → Term σ
| ⟨cfree v, _⟩ => Term.free (free_variable.free_variable v)
| ⟨cconst c, _⟩ => Term.const (Constant.Constant c)

theorem iso0{σ : Signature}: ∀ t:Term σ , decode0 σ (g t) = t:= by
intro term
cases term with
| free n=> unfold decode0
           unfold g
           simp
| const n=> unfold decode0
            unfold g
            simp

instance [Encodable ℕ] {σ : Signature}: Encodable (Term σ) := by
  haveI h: Encodable (construct) := by
    unfold construct
    exact inferInstance
  apply Encodable.ofLeftInverse (g) (decode0 σ) (iso0)
