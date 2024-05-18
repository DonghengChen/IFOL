import CLM.IFOL
import CLM.encode_formula

open IFOL
open Set
open Classical



lemma subset_proof {Γ :Set (Formula σ)}{r: Formula σ}(h: Γ ⊢ r)(hs: Γ ⊆ Γ'): (Γ' ⊢ r) := by
let Q := Γ' \ Γ
by_cases h0:Q=∅
have h1:Γ' = Γ := by apply eq_of_subset_of_subset;apply  Set.diff_eq_empty.mp;exact h0;exact hs
rw [h1] ;exact h
have h1:=Set.nonempty_iff_ne_empty.mpr h0
have h1:=Set.nonempty_def.mp h1
rcases h1 with ⟨f,hf⟩
have h2:= Proof.ref hf
have h3:= Proof.introA h h2
simp at h3
have h2:Γ ∪ Γ' = Γ' := by simp;exact hs
rw [h2] at h3
apply Proof.elimA1 h3

-- lemma subset_proof {Γ :Set (Formula σ)}{r: Formula σ}(h: Γ ⊢ r)(h0: Γ ⊆ Γ'): (Γ' ⊢ r) :=by
-- induction h generalizing Γ' with
-- | ref h1 => apply Proof.ref (h0 h1)
-- | introI h1 h2 => rename_i A B Δ
--                   apply Proof.introI
--                   apply h2
--                   apply Set.union_subset_union_left
--                   exact h0
-- | elimI h1 h2 h3 h4 => rename_i A B Δ
--                        apply Proof.elimI
--                        exact h3 h0
--                        apply h4 h0
-- | introA h1 h2 h3 h4 => rename_i A B Δ
--                         apply Proof.introA
--                         apply h3 h0
--                         apply h4 h0
-- | elimA1 h1 h2  =>      rename_i A B Δ
--                         apply Proof.elimA1
--                         apply h2 h0
-- | elimA2 h1 h2  =>      rename_i A B Δ
--                         apply Proof.elimA2
--                         apply h2 h0
-- | introO1 h1 h2 h3 =>   rename_i A Δ
--                         apply Proof.introO1
--                         apply h3 h0
-- | introO2 h1 h2 h3 =>   rename_i A Δ
--                         apply Proof.introO2
--                         apply h3 h0
-- | elimO h1 h2 h3 h4 h5 h6 => rename_i A B C Δ
--                              apply Proof.elimO
--                              apply h4 h0
--                              apply h5
--                              apply Set.union_subset_union_left;exact h0
--                              apply h6
--                              apply Set.union_subset_union_left;exact h0
-- | botE A h1 h2 =>    apply Proof.botE
--                      apply h2
--                      exact h0
-- | introF h1 h2 h3 => rename_i A Δ n
--                      apply Proof.introF
--                      exact h3 h0
--                      simp[free_terms] at h2
--                      simp[free_terms]
--                      intro x hx

--                      sorry
-- | elimF h1 h2 h3 =>
--                     apply Proof.elimF
--                     apply h3 h0
-- | introE h1 h2=>        apply Proof.introE
--                         apply h2 h0
-- | elimE h1 h2 h3 h4 h5 h6 => rename_i Δ A B C D
--                              simp at h0
--                              rw [← Set.union_eq_self_of_subset_right h0.2]
--                              apply Proof.elimE
--                              apply h5
--                              exact h0.1
--                              apply h6
--                              apply Set.union_subset_union_left
--                              rfl;
--                              exact h3
--                              exact h4













lemma cond_mono_proof {Γ :Set (Formula σ)}{r: Formula σ}(h: Γ ⊢ r): ∀ Q: Set (Formula σ), (Q ∪ Γ) ⊢ r :=by
intro Q
apply subset_proof h
simp

lemma cond_mono_proof2 {Γ :Set (Formula σ)}{r: Formula σ}(h: Γ ⊢ r): ∀ Q: Set (Formula σ), (Γ ∪ Q) ⊢ r :=by
intro Q
apply subset_proof h
simp


lemma temp{a b c d:Nat}(h:¬a = d)(h2:Prop): (d = a) → h2 := by intro h2; rw[h2] at h;by_contra;simp at h


lemma seq_subs (f: Formula σ):∀(u v:Term σ),f.Substitution u v = (f.Substitution u v).Substitution u v:= by
  induction f  with
  | atomic_formula r ts=>
    intro u v
    cases u<;>
    cases v<;>
    all_goals (simp[Formula.Substitution])
    all_goals (ext x)
    all_goals (generalize eq: (ts x) = d)
    all_goals (cases d)
    all_goals (simp[Term.Substitution])
    all_goals (split)
    all_goals (simp[*])
  | disjunction f1 f2 ih1 ih2=>
    intro u v
    cases u<;>
    cases v<;>
    all_goals (simp[Formula.Substitution])
    all_goals (constructor)
    any_goals (exact (ih1 _ _))
    any_goals (exact (ih2 _ _))
  | implication f1 f2 ih1 ih2=>
    intro u v
    cases u<;>
    cases v<;>
    all_goals (simp[Formula.Substitution])
    all_goals (constructor)
    any_goals (exact (ih1 _ _))
    any_goals (exact (ih2 _ _))
  | conjunction f1 f2 ih1 ih2=>
    intro u v
    cases u<;>
    cases v<;>
    all_goals (simp[Formula.Substitution])
    all_goals (constructor)
    any_goals (exact (ih1 _ _))
    any_goals (exact (ih2 _ _))
  | bottom => intro u v
              cases u<;>
              cases v<;>
              simp[Formula.Substitution]
  | existential_quantification f ih=>
    intro u v
    cases u<;>
    cases v<;>
    all_goals (simp[Formula.Substitution,Term.lift])
    all_goals (rename_i c d)
    all_goals (exact ih _ _)

  | universal_quantification f ih=>
    intro u v
    cases u<;>
    cases v<;>
    all_goals (simp[Formula.Substitution,Term.lift])
    all_goals (rename_i c d)
    all_goals (exact ih _ _)


-- lemma subs_comp {f: Formula σ}{u v w:Term σ}(h: v ∉ free_terms {f}):(f.Substitution u v).Substitution v w = f.Substitution u w:= by
--   induction f with
--   | atomic_formula r ts=>
--     simp[free_terms,Formula.free_terms] at h
--     cases v<;>
--     cases u<;>
--     cases w<;>
--     all_goals (simp[Formula.Substitution])
--     all_goals (ext x)
--     all_goals (have h4:= h x)
--     all_goals (generalize eq: (ts x) = d)
--     all_goals (cases d)
--     all_goals (rw[eq] at h4)
--     all_goals (simp[Term.free_terms] at h4)
--     all_goals (rename_i a b c d)
--     all_goals (simp[Term.Substitution])
--     all_goals (by_cases h3:d = b)
--     any_goals (simp[h3])
--     all_goals (intro h5)
--     any_goals (rw[h5] at h4)
--     any_goals (simp at h4)
--     any_goals (rw[h3,h5] at h4)
--     any_goals (simp at h4)
--   | conjunction f1 f2 ih1 ih2=>
--     simp[free_terms,Formula.free_terms] at h
--     push_neg at h
--     cases v<;>
--     cases u<;>
--     cases w<;>
--     all_goals (simp[Formula.Substitution])
--     all_goals (simp[free_terms]at ih1)
--     all_goals (simp[free_terms]at ih2)
--     all_goals (constructor)
--     any_goals (apply (ih1 h.1))
--     any_goals (apply (ih2 h.2))
--   | disjunction f1 f2 ih1 ih2=>
--     simp[free_terms,Formula.free_terms] at h
--     push_neg at h
--     cases v<;>
--     cases u<;>
--     cases w<;>
--     all_goals (simp[Formula.Substitution])
--     all_goals (simp[free_terms]at ih1)
--     all_goals (simp[free_terms]at ih2)
--     all_goals (constructor)
--     any_goals (apply (ih1 h.1))
--     any_goals (apply (ih2 h.2))
--   | implication f1 f2 ih1 ih2=>
--     simp[free_terms,Formula.free_terms] at h
--     push_neg at h
--     cases v<;>
--     cases u<;>
--     cases w<;>
--     all_goals (simp[Formula.Substitution])
--     all_goals (simp[free_terms]at ih1)
--     all_goals (simp[free_terms]at ih2)
--     all_goals (constructor)
--     any_goals (apply (ih1 h.1))
--     any_goals (apply (ih2 h.2))
--   | bottom => cases v<;>
--               cases u<;>
--               cases w<;>
--               simp[Formula.Substitution]
--   | existential_quantification f ih=>
--     simp[free_terms,Formula.free_terms] at h
--     push_neg at h
--     cases v<;>
--     cases u<;>
--     cases w<;>
--     all_goals (simp[Formula.Substitution,Term.lift])
--     all_goals (simp[free_terms,Term.lift]at ih)
--     all_goals (rename_i a b c)


--   | universal_quantification f ih=>
--     simp[free_terms,Formula.free_terms] at h
--     push_neg at h
--     cases v<;>
--     cases u<;>
--     cases w<;>
--     all_goals (simp[Formula.Substitution,Term.lift])
--     all_goals (simp[free_terms,Term.lift]at ih)
--     all_goals sorry
