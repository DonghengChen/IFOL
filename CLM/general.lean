import CLM.IFOL
import CLM.encode_formula

open IFOL
open Set
open Classical

lemma cond_mono_proof {Γ :Set (Formula σ)}{r: Formula σ}(h: Γ ⊢ r): ∀ Q: Set (Formula σ), (Q ∪ Γ) ⊢ r :=by
intro Q
by_cases h0:Q=∅
rw [h0];simp;exact h
have h1:=Set.nonempty_iff_ne_empty.mpr h0
have h1:=Set.nonempty_def.mp h1
rcases h1 with ⟨f,hf⟩
have h2:= Proof.ref hf
have h3:= Proof.introA  h2 h
rw [Set.union_comm Q Γ]
rw[Set.union_comm Γ Q]
apply Proof.elimA2 h3

lemma cond_mono_proof2 {Γ :Set (Formula σ)}{r: Formula σ}(h: Γ ⊢ r): ∀ Q: Set (Formula σ), (Γ ∪ Q) ⊢ r :=by
intro Q
rw [Set.union_comm]
apply cond_mono_proof
assumption

lemma subset_proof {Γ :Set (Formula σ)}{r: Formula σ}(h: Γ ⊢ r)(h2: Γ ⊆ Γ'): (Γ' ⊢ r) :=by
have z:= cond_mono_proof h Γ'
rw [Set.union_eq_self_of_subset_right] at z
exact z
assumption
