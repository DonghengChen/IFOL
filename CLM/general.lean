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

lemma temp{a b c d:Nat}(h:¬a = d)(h2:Prop): (d = a) → h2 := by intro h2; rw[h2] at h;by_contra;simp at h

lemma subs_comp {f: Formula σ}{u v w:Term σ}(h: v ∉ free_terms {f}):(f.Substitution u v).Substitution v w = f.Substitution u w:= by
  induction f with
  | atomic_formula r ts=>
    simp[free_terms,Formula.free_terms] at h
    cases v<;>
    cases u<;>
    cases w<;>
    simp[Formula.Substitution]<;>
    ext x<;>
    have h4:= h x<;>
    generalize eq: (ts x) = d<;>
    cases d <;>

    rw[eq] at h4<;>
    simp[Term.free_terms] at h4<;>
    rename_i a b c d<;>
    simp[Term.Substitution]<;>
    by_cases h3:d = b <;>
    try simp[h3]<;>
    try intro h5<;>
    
