import CLM.IFOL
import CLM.encodable

open IFOL
open encodable
open fin

private def construct:= ℕ ⊕ (ℕ × ℕ)
local notation "cfree" v => Sum.inl v
local notation "cconst" v => Sum.inr v

@[reducible]
private def arity: construct → Nat
| (cfree _) => 0
| (cconst _)  => 0

def g{σ : Signature}: Term σ → Wfin arity:=
fun term => match term with
| .free n => ⟨cfree n, mk_fn0⟩
| .const n m=> ⟨cconst ⟨n,m⟩, mk_fn0⟩


private def decode0(σ : Signature) :Wfin arity → Term σ
| ⟨cfree v, _⟩ => Term.free v
| ⟨cconst c, _⟩ => Term.const c.1 c.2

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
