import CLM.IFOL
import CLM.encode_formula
import CLM.general
import CLM.pigeon
import CLM.completeness
open IFOL
open Set
open Classical

def z_term {σ:Signature}(t: Term σ): Term σ :=
 match t with
 | .free n => .free n
 | .const c => .const (2*c+1)

def z_formula {σ:Signature}(φ: Formula σ): Formula σ :=
match φ with
| .atomic_formula r ts=> (# r) (fun x=> z_term (ts x))
| f1 →ᵢ f2 => (z_formula f1) →ᵢ (z_formula f2)
| f1 ∧ᵢ f2 => (z_formula f1) ∧ᵢ (z_formula f2)
| f1 ∨ᵢ f2 => (z_formula f1) ∨ᵢ (z_formula f2)
| ⊥ => ⊥
| ∃ᵢ f => ∃ᵢ z_formula f
| ∀ᵢ f => ∀ᵢ z_formula f

def z_set {σ:Signature}(Γ: Set (Formula σ)): Set (Formula σ) :=
⋃ (f ∈ Γ), {z_formula f}


def weak_provable{σ:Signature}(f: Formula σ): (∅⊢ f)↔ (∅ ⊢ (z_formula f)) := by
  constructor
  intro h
  
















def bi_provable {σ:Signature}(Γ: Set (Formula σ))(f: Formula σ): (Γ ⊢ f) ↔ ((z_set Γ) ⊢ (z_formula f)) := by
  constructor
  intro h
  have h1:= Finset_proof h
  rcases h1 with ⟨G,h2,h3,h4⟩
  suffices h5:z_set G ⊢ z_formula f
  apply subset_proof h5
  simp [z_set]
  intro i hi
  use i
  constructor
  exact h2 hi
  rfl
  induction h
  sorry
  simp[z_formula]
  apply Proof.introI


  sorry
  sorry
