import CLM.IFOL
import CLM.general
open IFOL
open Set
open Classical



lemma free_modify {σ : Signature}{M}(v:Term σ → M.A) :∀(m:Nat),∀(A:Formula σ){t w hw}, (hA: A.size ≤ m) → (h:Formula.force_form M w hw v A) → (h2: ¬Term.free n ∈ free_terms {A}) →
Formula.force_form M w hw (insert_value_function M v t) (Formula.iforce_Substitution (Formula.force_lift A) (n + 1)):= by
  intro m
  induction m
  intro A t w hw hA h h2
  simp at hA
  cases A
  any_goals (simp[Formula.size] at hA)
  case atomic_formula r ts =>

      unfold Formula.force_form at h
      simp only [Formula.force_form]
      suffices heq:(fun index => v (ts index))=(fun index =>insert_value_function M v t (match Term.lift 0 (ts index) with
                        | Term.free m => if n + 1 = m then Term.free 0 else Term.lift 0 (ts index)
                        | x => Term.lift 0 (ts index)))
      rw [heq] at h
      exact h
      ext x
      simp[insert_value_function]
      cases z:(ts x)
      simp[Term.lift]
      rename_i m
      split

      split
      rename_i a b c d
      by_cases hd:n=m
      simp[free_terms,Formula.free_terms,Term.free_terms] at h2
      have h22:= h2 x
      simp [z] at h22
      trivial
      simp [hd] at c
      rw [d] at c
      absurd d
      linarith
      rename_i a b c d
      by_cases hd:n=m
      simp[hd] at c
      symm at c
      trivial
      simp[hd] at c
      rw [← c]
      simp
      rename_i a b c
      by_cases hd:n=m
      simp[hd] at c
      simp[hd] at c
      rename_i m
      split
      rename_i a b c
      split
      any_goals (simp[Term.lift] at c)
      rename_i a b c
      any_goals (simp[Term.lift] at c)
      rw [c]
  case bottom => simp[Formula.force_form] at h
  rename_i m h1
  intro A t w hw hA h h2
  cases A with
  | atomic_formula r ts =>
      unfold Formula.force_form at h
      simp only [Formula.force_form]
      suffices heq:(fun index => v (ts index))=(fun index =>insert_value_function M v t (match Term.lift 0 (ts index) with
                        | Term.free m => if n + 1 = m then Term.free 0 else Term.lift 0 (ts index)
                        | x => Term.lift 0 (ts index)))
      rw [heq] at h
      exact h
      ext x
      simp[insert_value_function]
      cases z:(ts x)
      simp[Term.lift]
      rename_i m
      split

      split
      rename_i a b c d
      by_cases hd:n=m
      simp[free_terms,Formula.free_terms,Term.free_terms] at h2
      have h22:= h2 x
      simp [z] at h22
      trivial
      simp [hd] at c
      rw [d] at c
      absurd d
      linarith
      rename_i a b c d
      by_cases hd:n=m
      simp[hd] at c
      symm at c
      trivial
      simp[hd] at c
      rw [← c]
      simp
      rename_i a b c
      by_cases hd:n=m
      simp[hd] at c
      simp[hd] at c
      rename_i m
      split
      rename_i a b c
      split
      any_goals (simp[Term.lift] at c)
      rename_i a b c
      any_goals (simp[Term.lift] at c)
      rw [c]
  | conjunction f1 f2 =>
    simp[Formula.force_form] at h
    simp[Formula.force_form]
    constructor
    apply h1
    simp[Formula.size] at hA
    linarith
    exact h.1
    simp[free_terms] at h2
    simp[Formula.free_terms] at h2
    push_neg at h2
    simp[free_terms,Formula.free_terms]
    exact h2.1
    apply h1
    simp[Formula.size] at hA
    linarith
    exact h.2
    simp[free_terms] at h2
    simp[Formula.free_terms] at h2
    push_neg at h2
    simp[free_terms,Formula.free_terms]
    exact h2.2
  | disjunction f1 f2 h1 h3=>
    simp[Formula.force_form] at h
    simp[Formula.force_form]
    cases h
    case inl he=> left;apply h1;simp[Formula.size] at hA;exact he
                  simp[free_terms] at h2
                  simp[Formula.free_terms] at h2
                  push_neg at h2
                  simp[free_terms,Formula.free_terms]
                  exact h2.1
    case inr he=> right;apply h3;exact he
                  simp[free_terms] at h2
                  simp[Formula.free_terms] at h2
                  push_neg at h2
                  simp[free_terms,Formula.free_terms]
                  exact h2.2
  | bottom =>apply h
  | implication f1 f2 h1 h3=>
    simp[Formula.force_form] at h
    simp[Formula.force_form]
    intro u hs ha
    apply h3
    apply h

    sorry
  | existential_quantification f h1=>
    simp[Formula.force_lift,Formula.iforce_Substitution]
    simp[Formula.force_form] at h
    rcases h with ⟨t,ht⟩
    have h1:= h1 ht









































def soundness {σ : Signature}(Γ : Set (Formula σ))(f : Formula σ) : (Γ ⊢ f) → (Γ ⊧ f) := fun h=> by
  induction h with
  | ref h => rename_i A Δ;
             intro M w v hw hf
             exact hf _ h
  | introI h ih => rename_i A B Δ
                   intro M w v hw hf
                   simp[Formula.force_form]
                   have hi:= ih M w v hw
                   intro u Ru hu
                   have hi2:= ih M u v (M.R_closed w u Ru hw)
                   apply hi2
                   intro f hf
                   cases hf with
                   | inl hin => apply Formula.mono_proof _ _ _ Ru f hw;apply hf; exact hin
                   | inr hif => simp at hif;rw[hif];exact hu
  | elimI h ih     => rename_i A B Δ h1 h2
                      intro M w v hw hf
                      have hi1:= h1 M w v hw hf
                      have hi2:= h2 M w v hw hf
                      simp[Formula.force_form] at hi1
                      apply hi1
                      exact hi2
                      apply M.refl
                      exact hw
  | botE h h1 h2 => rename_i Δ
                    intro M w v hw hf
                    have hi1:= h2 M w v hw hf
                    simp[Formula.force_form] at hi1
  | introA h1 h2 h3 h4 =>
    rename_i A B Δ
    intro M w v hw hf
    simp[Formula.force_form]
    constructor
    exact h3 M w v hw hf
    exact h4 M w v hw hf
  | elimA1 h1 h2 =>
    rename_i A B Δ
    intro M w v hw hf
    exact (h2 M w v hw hf).left
  | elimA2 h1 h2 =>
    rename_i A B Δ
    intro M w v hw hf
    exact (h2 M w v hw hf).right
  | introO1 A h2 =>
    rename_i B Δ h
    intro M w v hw hf
    simp[Formula.force_form]
    left
    exact h M w v hw hf
  | introO2 A h2 =>
    rename_i B Δ h
    intro M w v hw hf
    simp[Formula.force_form]
    right
    exact h M w v hw hf
  | elimO h1 h2 h3 h4 h5 h6=>
    rename_i A B C Δ
    intro M w v hw hf
    have h4:= h4 M w v hw hf
    cases h4 with
    | inl hfl => have h5:= h5 M w v hw
                 apply h5
                 intro f hs
                 cases hs with
                 | inl hss=> exact hf _ hss
                 | inr hss=> simp at hss;rw[hss];exact hfl
    | inr hfr => have h6:= h6 M w v hw
                 apply h6
                 intro f hs
                 cases hs with
                 | inl hss=> exact hf _ hss
                 | inr hss=> simp at hss;rw[hss];exact hfr
  | introF h1 h2 h3 =>
    rename_i A Δ n
    intro M w v hw hf
    simp[Formula.force_form]
    have h4:= h3 M w v hw hf
    intro t
