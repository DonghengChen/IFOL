/- Constant generalization.

`Term.cv c x d` / `Formula.cv c x d` replace the constant `c` by the free
variable `x` (capture-avoidingly: at binder depth `d` the variable is inserted
as index `x + d`).

Main results:
- `subst_cv`   : a derivation from a FINITE context survives the substitution
                 `const c ↦ free x`, provided `x` is fresh for the context and
                 the conclusion.  The proof induction handles eigenvariable
                 collisions by running each case at a super-fresh variable `x'`
                 and swapping `x ↔ x'` (via `swf_proof`) at the end.
- `const_gen`  : if `Γ ⊢ A.inst (const c)` with `c` fresh for `Γ` and `A`,
                 then `Γ ⊢ ∀ᵢ A`.  This is the admissible rule needed by the
                 ∀-case of the canonical-model truth lemma. -/

import CLM.IFOL
import CLM.proof_lemmas
import CLM.henkin
import CLM.const_rename
import CLM.var_swap
open IFOL
open Set
open Classical

namespace IFOL

variable {σ : Signature}

/- ### The substitution `const c ↦ free x` -/

def Term.cv (c x d : ℕ) : Term σ → Term σ
  | .free n => .free n
  | .const e => if e = c then .free (x + d) else .const e

def Formula.cv (c x d : ℕ) : Formula σ → Formula σ
  | .atomic_formula r ts => .atomic_formula r (fun i => (ts i).cv c x d)
  | .conjunction f1 f2 => .conjunction (f1.cv c x d) (f2.cv c x d)
  | .disjunction f1 f2 => .disjunction (f1.cv c x d) (f2.cv c x d)
  | .implication f1 f2 => .implication (f1.cv c x d) (f2.cv c x d)
  | .existential_quantification f => .existential_quantification (f.cv c x (d+1))
  | .universal_quantification f => .universal_quantification (f.cv c x (d+1))
  | .bottom => .bottom

/- ### Computation helpers (Lean 4.0.0: unfold leaves match terms; use `show`) -/

private lemma cv_free {c x d n : ℕ} :
    Term.cv c x d (Term.free n : Term σ) = Term.free n := rfl

private lemma cv_const_eq {c x d e : ℕ} (h : e = c) :
    Term.cv c x d (Term.const e : Term σ) = Term.free (x + d) := by
  show (if e = c then (Term.free (x+d) : Term σ) else Term.const e) = Term.free (x+d)
  rw [if_pos h]

private lemma cv_const_ne {c x d e : ℕ} (h : ¬ e = c) :
    Term.cv c x d (Term.const e : Term σ) = Term.const e := by
  show (if e = c then (Term.free (x+d) : Term σ) else Term.const e) = Term.const e
  rw [if_neg h]

private lemma lift_free_lt {k n : ℕ} (h : n < k) :
    Term.lift k (Term.free n : Term σ) = Term.free n := by
  show (if n < k then (Term.free n : Term σ) else Term.free (n+1)) = Term.free n
  rw [if_pos h]

private lemma lift_free_ge {k n : ℕ} (h : ¬ n < k) :
    Term.lift k (Term.free n : Term σ) = Term.free (n+1) := by
  show (if n < k then (Term.free n : Term σ) else Term.free (n+1)) = Term.free (n+1)
  rw [if_neg h]

private lemma down_free_lt {k n : ℕ} (h : n < k) :
    Term.down k (Term.free n : Term σ) = Term.free n := by
  show (if n < k then (Term.free n : Term σ) else Term.free (n-1)) = Term.free n
  rw [if_pos h]

private lemma down_free_ge {k n : ℕ} (h : ¬ n < k) :
    Term.down k (Term.free n : Term σ) = Term.free (n-1) := by
  show (if n < k then (Term.free n : Term σ) else Term.free (n-1)) = Term.free (n-1)
  rw [if_neg h]

private lemma subst_free_eq {n j : ℕ} (e : Term σ) (h : n = j) :
    Term.Substitution (Term.free n) (Term.free j) e = e := by
  show (if n = j then e else Term.free n) = e
  rw [if_pos h]

private lemma subst_free_ne {n j : ℕ} (e : Term σ) (h : ¬ n = j) :
    Term.Substitution (Term.free n) (Term.free j) e = Term.free n := by
  show (if n = j then e else Term.free n) = Term.free n
  rw [if_neg h]

private lemma subst_const {j : ℕ} (e : Term σ) (m : ℕ) :
    Term.Substitution (Term.const m) (Term.free j) e = Term.const m := rfl

private lemma ft_free_ge {z d : ℕ} (h : z ≥ d) :
    Term.free_terms (Term.free z : Term σ) d = {Term.free (z-d)} := by
  show (if z ≥ d then ({Term.free (z-d)} : Set (Term σ)) else ∅) = {Term.free (z-d)}
  rw [if_pos h]

private lemma ft_free_lt {z d : ℕ} (h : ¬ z ≥ d) :
    Term.free_terms (Term.free z : Term σ) d = ∅ := by
  show (if z ≥ d then ({Term.free (z-d)} : Set (Term σ)) else ∅) = ∅
  rw [if_neg h]

/- ### Fresh variable chooser -/

lemma exists_fresh_var (S : Set (Term σ)) (h : S.Finite) :
    ∃ x : ℕ, ∀ y : ℕ, x ≤ y → Term.free y ∉ S := by
  have him : ((fun t : Term σ => match t with
      | Term.free n => n + 1
      | Term.const _ => 0) '' S).Finite := Set.Finite.image _ h
  obtain ⟨N, hN⟩ := Set.Finite.bddAbove him
  refine ⟨N + 1, ?_⟩
  intro y hy hyS
  have h1 : y + 1 ≤ N := hN (Set.mem_image_of_mem _ hyS)
  linarith

/- ### `cv` is the identity when the constant does not occur -/

lemma cv_id_of_no_const {c x : ℕ} {f : Formula σ} (h : c ∉ f.consts) :
    ∀ d, Formula.cv c x d f = f := by
  induction f with
  | atomic_formula r ts =>
    intro d
    simp only [Formula.cv]
    congr 1
    funext i
    cases hti : ts i with
    | free n => exact cv_free
    | const e =>
      apply cv_const_ne
      intro hec
      apply h
      simp only [Formula.consts]
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      rw [hti]
      exact Set.mem_singleton_iff.mpr hec.symm
  | conjunction f1 f2 ih1 ih2 =>
    intro d
    simp only [Formula.cv]
    rw [ih1 (fun hc => h (Set.mem_union_left _ hc)) d,
      ih2 (fun hc => h (Set.mem_union_right _ hc)) d]
  | disjunction f1 f2 ih1 ih2 =>
    intro d
    simp only [Formula.cv]
    rw [ih1 (fun hc => h (Set.mem_union_left _ hc)) d,
      ih2 (fun hc => h (Set.mem_union_right _ hc)) d]
  | implication f1 f2 ih1 ih2 =>
    intro d
    simp only [Formula.cv]
    rw [ih1 (fun hc => h (Set.mem_union_left _ hc)) d,
      ih2 (fun hc => h (Set.mem_union_right _ hc)) d]
  | existential_quantification f ih =>
    intro d
    simp only [Formula.cv]
    rw [ih h (d+1)]
  | universal_quantification f ih =>
    intro d
    simp only [Formula.cv]
    rw [ih h (d+1)]
  | bottom => intro d; rfl

/- ### Commutation with instantiation and generalization -/

lemma cv_term_lift {c x k d : ℕ} (hk : k ≤ d) (t : Term σ) :
    Term.cv c x (d+1) (Term.lift k t) = Term.lift k (Term.cv c x d t) := by
  cases t with
  | free n =>
    rw [cv_free]
    by_cases h1 : n < k
    · rw [lift_free_lt h1, cv_free]
    · rw [lift_free_ge h1, cv_free]
  | const e =>
    by_cases h1 : e = c
    · have hxk : ¬ x + d < k := by intro h; linarith
      rw [show Term.lift k (Term.const e : Term σ) = Term.const e from rfl,
        cv_const_eq h1, cv_const_eq h1, lift_free_ge hxk]
      rfl
    · rw [show Term.lift k (Term.const e : Term σ) = Term.const e from rfl,
        cv_const_ne h1, cv_const_ne h1]
      rfl

lemma cv_lift {c x k d : ℕ} (hk : k ≤ d) (f : Formula σ) :
    Formula.cv c x (d+1) (f.lift k) = (Formula.cv c x d f).lift k := by
  induction f generalizing k d with
  | atomic_formula r ts =>
    simp only [Formula.lift, Formula.cv]
    congr 1
    funext i
    exact cv_term_lift hk _
  | conjunction f1 f2 ih1 ih2 =>
    simp only [Formula.lift, Formula.cv]; rw [ih1 hk, ih2 hk]
  | disjunction f1 f2 ih1 ih2 =>
    simp only [Formula.lift, Formula.cv]; rw [ih1 hk, ih2 hk]
  | implication f1 f2 ih1 ih2 =>
    simp only [Formula.lift, Formula.cv]; rw [ih1 hk, ih2 hk]
  | existential_quantification f ih =>
    simp only [Formula.lift, Formula.cv]; rw [ih (Nat.succ_le_succ hk)]
  | universal_quantification f ih =>
    simp only [Formula.lift, Formula.cv]; rw [ih (Nat.succ_le_succ hk)]
  | bottom => rfl

private lemma cv_subst_down_term {c x : ℕ} (j d : ℕ) (hjd : j ≤ d) (t e : Term σ)
    (he : ∀ m, e = Term.free m → j < m) :
    Term.cv c x d (Term.down j (Term.Substitution t (Term.free j) e))
      = Term.down j (Term.Substitution (Term.cv c x (d+1) t) (Term.free j) (Term.cv c x (d+1) e)) := by
  cases t with
  | const q =>
    rw [subst_const]
    by_cases h1 : q = c
    · have hnj : ¬ x + (d+1) = j := by intro h; linarith
      have hnlt : ¬ x + (d+1) < j := by intro h; linarith
      rw [show Term.down j (Term.const q : Term σ) = Term.const q from rfl,
        cv_const_eq h1, cv_const_eq h1, subst_free_ne _ hnj, down_free_ge hnlt]
      rfl
    · rw [show Term.down j (Term.const q : Term σ) = Term.const q from rfl,
        cv_const_ne h1, cv_const_ne h1, subst_const]
      rfl
  | free n =>
    by_cases h1 : n = j
    · rw [subst_free_eq e h1, cv_free, subst_free_eq _ h1]
      cases e with
      | free m =>
        have hm := he m rfl
        have hmj : ¬ m < j := by intro h; linarith
        rw [down_free_ge hmj, cv_free, cv_free, down_free_ge hmj]
      | const q =>
        by_cases h2 : q = c
        · have hnlt : ¬ x + (d+1) < j := by intro h; linarith
          rw [show Term.down j (Term.const q : Term σ) = Term.const q from rfl,
            cv_const_eq h2, cv_const_eq h2, down_free_ge hnlt]
          rfl
        · rw [show Term.down j (Term.const q : Term σ) = Term.const q from rfl,
            cv_const_ne h2, cv_const_ne h2]
          rfl
    · rw [subst_free_ne e h1, cv_free, subst_free_ne _ h1]
      by_cases h2 : n < j
      · rw [down_free_lt h2, cv_free]
      · rw [down_free_ge h2, cv_free]

/-- Core commutation: `cv` past `Substitution (free j) e; down j`, where `e`
mentions no free index `≤ j`. -/
lemma cv_inst_aux {c x : ℕ} :
    ∀ (A : Formula σ) (j d : ℕ) (e : Term σ), j ≤ d →
    (∀ m, e = Term.free m → j < m) →
    Formula.cv c x d ((A.Substitution (Term.free j) e).down j)
      = ((Formula.cv c x (d+1) A).Substitution (Term.free j) (Term.cv c x (d+1) e)).down j := by
  intro A
  induction A with
  | atomic_formula r ts =>
    intro j d e hjd he
    simp only [Formula.Substitution, Formula.down, Formula.cv]
    congr 1
    funext i
    exact cv_subst_down_term j d hjd (ts i) e he
  | conjunction f1 f2 ih1 ih2 =>
    intro j d e hjd he
    simp only [Formula.Substitution, Formula.down, Formula.cv]
    rw [ih1 j d e hjd he, ih2 j d e hjd he]
  | disjunction f1 f2 ih1 ih2 =>
    intro j d e hjd he
    simp only [Formula.Substitution, Formula.down, Formula.cv]
    rw [ih1 j d e hjd he, ih2 j d e hjd he]
  | implication f1 f2 ih1 ih2 =>
    intro j d e hjd he
    simp only [Formula.Substitution, Formula.down, Formula.cv]
    rw [ih1 j d e hjd he, ih2 j d e hjd he]
  | existential_quantification f ih =>
    intro j d e hjd he
    simp only [Formula.Substitution, Formula.down, Formula.cv]
    have hl : ((Term.free j).lift 0 : Term σ) = Term.free (j+1) :=
      lift_free_ge (Nat.not_lt_zero j)
    have he' : ∀ m, e.lift 0 = Term.free m → j+1 < m := by
      intro m hm
      cases e with
      | const c => exact absurd hm (by unfold Term.lift; simp)
      | free m0 =>
        rw [lift_free_ge (Nat.not_lt_zero m0)] at hm
        injection hm with hm'
        have := he m0 rfl
        linarith
    rw [hl, ih (j+1) (d+1) (e.lift 0) (Nat.succ_le_succ hjd) he',
      cv_term_lift (Nat.zero_le (d+1)) e]
  | universal_quantification f ih =>
    intro j d e hjd he
    simp only [Formula.Substitution, Formula.down, Formula.cv]
    have hl : ((Term.free j).lift 0 : Term σ) = Term.free (j+1) :=
      lift_free_ge (Nat.not_lt_zero j)
    have he' : ∀ m, e.lift 0 = Term.free m → j+1 < m := by
      intro m hm
      cases e with
      | const c => exact absurd hm (by unfold Term.lift; simp)
      | free m0 =>
        rw [lift_free_ge (Nat.not_lt_zero m0)] at hm
        injection hm with hm'
        have := he m0 rfl
        linarith
    rw [hl, ih (j+1) (d+1) (e.lift 0) (Nat.succ_le_succ hjd) he',
      cv_term_lift (Nat.zero_le (d+1)) e]
  | bottom => intro j d e hjd he; rfl

lemma cv_inst (c x d : ℕ) (A : Formula σ) (τ : Term σ) :
    Formula.cv c x d (A.inst τ)
      = (Formula.cv c x (d+1) A).inst (Term.cv c x d τ) := by
  unfold Formula.inst
  have he : ∀ m, τ.lift 0 = Term.free m → 0 < m := by
    intro m hm
    cases τ with
    | const c => exact absurd hm (by unfold Term.lift; simp)
    | free m0 =>
      rw [lift_free_ge (Nat.not_lt_zero m0)] at hm
      injection hm with hm'
      rw [← hm']
      exact Nat.succ_pos m0
  rw [cv_inst_aux A 0 d (τ.lift 0) (Nat.zero_le d) he,
    cv_term_lift (Nat.zero_le d) τ]

private lemma cv_gen_term {c x y : ℕ} (hxy : y ≠ x) (t : Term σ) (j : ℕ) :
    Term.cv c x (j+1) (Term.Substitution t (Term.free (y+j+1)) (Term.free j))
      = Term.Substitution (Term.cv c x (j+1) t) (Term.free (y+j+1)) (Term.free j) := by
  cases t with
  | free n =>
    rw [cv_free]
    by_cases h1 : n = y+j+1
    · rw [subst_free_eq _ h1, cv_free]
    · rw [subst_free_ne _ h1, cv_free]
  | const q =>
    by_cases h1 : q = c
    · have hne : ¬ x + (j+1) = y+j+1 := by intro h; apply hxy; linarith
      rw [subst_const, cv_const_eq h1, subst_free_ne _ hne]
    · rw [subst_const, cv_const_ne h1, subst_const]

/-- `cv` commutes with the substitution underlying `gen y`, provided `y ≠ x`. -/
lemma cv_gen_aux {c x y : ℕ} (hxy : y ≠ x) :
    ∀ (A : Formula σ) (j : ℕ),
    Formula.cv c x (j+1) (A.Substitution (Term.free (y+j+1)) (Term.free j))
      = (Formula.cv c x (j+1) A).Substitution (Term.free (y+j+1)) (Term.free j) := by
  intro A
  induction A with
  | atomic_formula r ts =>
    intro j
    simp only [Formula.Substitution, Formula.cv]
    congr 1
    funext i
    exact cv_gen_term hxy (ts i) j
  | conjunction f1 f2 ih1 ih2 =>
    intro j
    simp only [Formula.Substitution, Formula.cv]
    rw [ih1 j, ih2 j]
  | disjunction f1 f2 ih1 ih2 =>
    intro j
    simp only [Formula.Substitution, Formula.cv]
    rw [ih1 j, ih2 j]
  | implication f1 f2 ih1 ih2 =>
    intro j
    simp only [Formula.Substitution, Formula.cv]
    rw [ih1 j, ih2 j]
  | existential_quantification f ih =>
    intro j
    simp only [Formula.Substitution, Formula.cv]
    have hA : ((Term.free (y+j+1)).lift 0 : Term σ) = Term.free (y+(j+1)+1) :=
      lift_free_ge (Nat.not_lt_zero _)
    have hj : ((Term.free j).lift 0 : Term σ) = Term.free (j+1) :=
      lift_free_ge (Nat.not_lt_zero _)
    rw [hA, hj, ih (j+1)]
  | universal_quantification f ih =>
    intro j
    simp only [Formula.Substitution, Formula.cv]
    have hA : ((Term.free (y+j+1)).lift 0 : Term σ) = Term.free (y+(j+1)+1) :=
      lift_free_ge (Nat.not_lt_zero _)
    have hj : ((Term.free j).lift 0 : Term σ) = Term.free (j+1) :=
      lift_free_ge (Nat.not_lt_zero _)
    rw [hA, hj, ih (j+1)]
  | bottom => intro j; rfl

lemma cv_gen {c x y : ℕ} (hxy : y ≠ x) (A : Formula σ) :
    Formula.cv c x 1 (A.gen y) = (Formula.cv c x 0 A).gen y := by
  unfold Formula.gen
  have h := cv_gen_aux (c := c) (x := x) hxy (A.lift 0) 0
  rw [cv_lift (le_refl 0)] at h
  exact h

/- ### Free terms of a `cv`-image -/

private lemma mem_ft_cv_term {c x : ℕ} {s t : Term σ} {d : ℕ}
    (h : t ∈ (Term.cv c x d s).free_terms d) :
    t = Term.free x ∨ (t ∈ s.free_terms d ∧ t ≠ Term.const c) := by
  cases s with
  | free n =>
    rw [cv_free] at h
    by_cases h1 : n ≥ d
    · rw [ft_free_ge h1] at h
      have ht : t = Term.free (n-d) := Set.eq_of_mem_singleton h
      right
      refine ⟨by rw [ft_free_ge h1]; exact h, ?_⟩
      rw [ht]
      intro hc
      exact Term.noConfusion hc
    · rw [ft_free_lt h1] at h
      exact absurd h (Set.not_mem_empty _)
  | const e =>
    by_cases h1 : e = c
    · rw [cv_const_eq h1, ft_free_ge (Nat.le_add_left d x)] at h
      have ht : t = Term.free (x+d-d) := Set.eq_of_mem_singleton h
      left
      rw [ht, Nat.add_sub_cancel]
    · rw [cv_const_ne h1] at h
      have ht : t = Term.const e := Set.eq_of_mem_singleton h
      right
      refine ⟨h, ?_⟩
      rw [ht]
      intro hc
      injection hc with hc'
      exact h1 hc'

/-- Any free term of `cv c x d f` (at matching bound) is either the inserted
variable `x` or a free term of `f` other than `const c`. -/
lemma mem_ft_cv {c x : ℕ} {f : Formula σ} {t : Term σ} :
    ∀ {d : ℕ}, t ∈ (Formula.cv c x d f).free_terms d →
      t = Term.free x ∨ (t ∈ f.free_terms d ∧ t ≠ Term.const c) := by
  induction f with
  | atomic_formula r ts =>
    intro d h
    simp only [Formula.cv, Formula.free_terms] at h
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
    rcases mem_ft_cv_term hi with h1 | ⟨h2, h3⟩
    · exact Or.inl h1
    · exact Or.inr ⟨Set.mem_iUnion.mpr ⟨i, h2⟩, h3⟩
  | conjunction f1 f2 ih1 ih2 =>
    intro d h
    simp only [Formula.cv, Formula.free_terms] at h
    rcases h with h | h
    · rcases ih1 h with h1 | ⟨h2, h3⟩
      · exact Or.inl h1
      · exact Or.inr ⟨Set.mem_union_left _ h2, h3⟩
    · rcases ih2 h with h1 | ⟨h2, h3⟩
      · exact Or.inl h1
      · exact Or.inr ⟨Set.mem_union_right _ h2, h3⟩
  | disjunction f1 f2 ih1 ih2 =>
    intro d h
    simp only [Formula.cv, Formula.free_terms] at h
    rcases h with h | h
    · rcases ih1 h with h1 | ⟨h2, h3⟩
      · exact Or.inl h1
      · exact Or.inr ⟨Set.mem_union_left _ h2, h3⟩
    · rcases ih2 h with h1 | ⟨h2, h3⟩
      · exact Or.inl h1
      · exact Or.inr ⟨Set.mem_union_right _ h2, h3⟩
  | implication f1 f2 ih1 ih2 =>
    intro d h
    simp only [Formula.cv, Formula.free_terms] at h
    rcases h with h | h
    · rcases ih1 h with h1 | ⟨h2, h3⟩
      · exact Or.inl h1
      · exact Or.inr ⟨Set.mem_union_left _ h2, h3⟩
    · rcases ih2 h with h1 | ⟨h2, h3⟩
      · exact Or.inl h1
      · exact Or.inr ⟨Set.mem_union_right _ h2, h3⟩
  | existential_quantification f ih =>
    intro d h
    exact ih h
  | universal_quantification f ih =>
    intro d h
    exact ih h
  | bottom =>
    intro d h
    exact absurd h (Set.not_mem_empty _)

lemma cv_not_mem_set_ft_var {c x y : ℕ} (hxy : y ≠ x) {Γ : Set (Formula σ)}
    (h : Term.free y ∉ Set.free_terms Γ) :
    Term.free y ∉ Set.free_terms ((Formula.cv c x 0) '' Γ) := by
  intro hc
  unfold Set.free_terms at hc
  rw [Set.biUnion_image] at hc
  obtain ⟨g, hg, hmem⟩ := Set.mem_iUnion₂.mp hc
  rcases mem_ft_cv hmem with h1 | ⟨h2, _⟩
  · injection h1 with h1'
    exact hxy h1'
  · exact h (Set.mem_iUnion₂.mpr ⟨g, hg, h2⟩)

/- ### Swapping the target variable of a `cv`-image -/

private lemma swf_free_eq {a b d n : ℕ} (h : n = a + d) :
    Term.swf a b d (Term.free n : Term σ) = Term.free (b + d) := by
  show (if n = a + d then (Term.free (b+d) : Term σ)
    else if n = b + d then Term.free (a+d) else Term.free n) = Term.free (b+d)
  rw [if_pos h]

private lemma swf_free_eq' {a b d n : ℕ} (h1 : ¬ n = a + d) (h2 : n = b + d) :
    Term.swf a b d (Term.free n : Term σ) = Term.free (a + d) := by
  show (if n = a + d then (Term.free (b+d) : Term σ)
    else if n = b + d then Term.free (a+d) else Term.free n) = Term.free (a+d)
  rw [if_neg h1, if_pos h2]

private lemma swf_free_ne {a b d n : ℕ} (h1 : ¬ n = a + d) (h2 : ¬ n = b + d) :
    Term.swf a b d (Term.free n : Term σ) = Term.free n := by
  show (if n = a + d then (Term.free (b+d) : Term σ)
    else if n = b + d then Term.free (a+d) else Term.free n) = Term.free n
  rw [if_neg h1, if_neg h2]

private lemma swf_cv_term {c x x' : ℕ} (t : Term σ) (d : ℕ)
    (hx : Term.free x ∉ t.free_terms d) (hx' : Term.free x' ∉ t.free_terms d) :
    Term.swf x x' d (Term.cv c x' d t) = Term.cv c x d t := by
  cases t with
  | free n =>
    rw [cv_free, cv_free]
    have hna : ¬ n = x + d := by
      intro hh
      apply hx
      rw [ft_free_ge (show n ≥ d from by rw [hh]; exact Nat.le_add_left d x), hh,
        Nat.add_sub_cancel]
      rfl
    have hnb : ¬ n = x' + d := by
      intro hh
      apply hx'
      rw [ft_free_ge (show n ≥ d from by rw [hh]; exact Nat.le_add_left d x'), hh,
        Nat.add_sub_cancel]
      rfl
    exact swf_free_ne hna hnb
  | const q =>
    by_cases h1 : q = c
    · rw [cv_const_eq h1, cv_const_eq h1]
      by_cases hxx : x' = x
      · rw [hxx, swf_free_eq rfl]
      · have h2 : ¬ x' + d = x + d := by intro hh; apply hxx; linarith
        exact swf_free_eq' h2 rfl
    · rw [cv_const_ne h1, cv_const_ne h1]
      rfl

/-- If neither `x` nor `x'` occurs (at bound `d`), swapping them re-targets the
substitution: `swf x x' (cv c x' f) = cv c x f`. -/
lemma swf_cv {c x x' : ℕ} :
    ∀ (f : Formula σ) (d : ℕ),
    Term.free x ∉ f.free_terms d → Term.free x' ∉ f.free_terms d →
    Formula.swf x x' d (Formula.cv c x' d f) = Formula.cv c x d f := by
  intro f
  induction f with
  | atomic_formula r ts =>
    intro d hx hx'
    simp only [Formula.cv, Formula.swf]
    congr 1
    funext i
    apply swf_cv_term
    · exact fun hc => hx (Set.mem_iUnion.mpr ⟨i, hc⟩)
    · exact fun hc => hx' (Set.mem_iUnion.mpr ⟨i, hc⟩)
  | conjunction f1 f2 ih1 ih2 =>
    intro d hx hx'
    simp only [Formula.cv, Formula.swf]
    rw [ih1 d (fun hc => hx (Set.mem_union_left _ hc)) (fun hc => hx' (Set.mem_union_left _ hc)),
      ih2 d (fun hc => hx (Set.mem_union_right _ hc)) (fun hc => hx' (Set.mem_union_right _ hc))]
  | disjunction f1 f2 ih1 ih2 =>
    intro d hx hx'
    simp only [Formula.cv, Formula.swf]
    rw [ih1 d (fun hc => hx (Set.mem_union_left _ hc)) (fun hc => hx' (Set.mem_union_left _ hc)),
      ih2 d (fun hc => hx (Set.mem_union_right _ hc)) (fun hc => hx' (Set.mem_union_right _ hc))]
  | implication f1 f2 ih1 ih2 =>
    intro d hx hx'
    simp only [Formula.cv, Formula.swf]
    rw [ih1 d (fun hc => hx (Set.mem_union_left _ hc)) (fun hc => hx' (Set.mem_union_left _ hc)),
      ih2 d (fun hc => hx (Set.mem_union_right _ hc)) (fun hc => hx' (Set.mem_union_right _ hc))]
  | existential_quantification f ih =>
    intro d hx hx'
    simp only [Formula.cv, Formula.swf]
    rw [ih (d+1) hx hx']
  | universal_quantification f ih =>
    intro d hx hx'
    simp only [Formula.cv, Formula.swf]
    rw [ih (d+1) hx hx']
  | bottom => intro d hx hx'; rfl

lemma swf_cv_set {c x x' : ℕ} {Γ : Set (Formula σ)}
    (hx : Term.free x ∉ Set.free_terms Γ) (hx' : Term.free x' ∉ Set.free_terms Γ) :
    (Formula.swf x x' 0) '' ((Formula.cv c x' 0) '' Γ) = (Formula.cv c x 0) '' Γ := by
  rw [← Set.image_comp]
  apply Set.image_congr
  intro g hg
  show Formula.swf x x' 0 (Formula.cv c x' 0 g) = Formula.cv c x 0 g
  apply swf_cv g 0
  · exact fun hc => hx (Set.mem_iUnion₂.mpr ⟨g, hg, hc⟩)
  · exact fun hc => hx' (Set.mem_iUnion₂.mpr ⟨g, hg, hc⟩)

/- ### The substitution theorem -/

private lemma set_ft_union {Γ Δ : Set (Formula σ)} :
    Set.free_terms (Γ ∪ Δ) = Set.free_terms Γ ∪ Set.free_terms Δ := by
  unfold Set.free_terms
  exact Set.biUnion_union Γ Δ _

private lemma set_ft_union_singleton {Γ : Set (Formula σ)} {A : Formula σ} :
    Set.free_terms (Γ ∪ {A}) = Set.free_terms Γ ∪ A.free_terms 0 := by
  unfold Set.free_terms
  rw [Set.biUnion_union, Set.biUnion_singleton]

private lemma set_ft_mono {Γ Γ' : Set (Formula σ)} (h : Γ ⊆ Γ') :
    Set.free_terms Γ ⊆ Set.free_terms Γ' := by
  intro t ht
  obtain ⟨g, hg, hmem⟩ := Set.mem_iUnion₂.mp ht
  exact Set.mem_iUnion₂.mpr ⟨g, h hg, hmem⟩

/-- A derivation from a finite context survives `const c ↦ free x` for `x`
fresh for the context and the conclusion.

Proof strategy (per case of the induction): the "easy" cases (where every
premise formula sits inside the conclusion or the context) apply the IH at `x`
directly.  The cases with internal cut formulas (elimI, elimA*, elimO, introF,
elimF, introE, elimE) apply the IH at a super-fresh `x'` (obtained from
`exists_fresh_var` — all contexts are finite), assemble the conclusion at `x'`,
and finish with `swf_proof` (swap `x ↔ x'`), which restores the target `x`
because neither `x` (hypothesis) nor `x'` (super-freshness) occurs in the final
context or conclusion (`swf_cv`, `swf_cv_set`). -/
theorem subst_cv {Γ : Set (Formula σ)} {B : Formula σ} (h : Γ ⊢ B) :
    ∀ (c x : ℕ), Γ.Finite →
    (Term.free x) ∉ Set.free_terms Γ →
    (Term.free x) ∉ Formula.free_terms B 0 →
    ((Formula.cv c x 0) '' Γ) ⊢ (Formula.cv c x 0 B) := by
  induction h with
  | ref hm =>
    intro c x hfin hxΓ hxB
    exact Proof.ref (Set.mem_image_of_mem _ hm)
  | introI h ih =>
    intro c x hfin hxΓ hxB
    rename_i A B0 Γ0
    have hxA : Term.free x ∉ Formula.free_terms A 0 :=
      fun hc => hxB (Set.mem_union_left _ hc)
    have hxB0 : Term.free x ∉ Formula.free_terms B0 0 :=
      fun hc => hxB (Set.mem_union_right _ hc)
    have hxΓA : Term.free x ∉ Set.free_terms (Γ0 ∪ {A}) := by
      rw [set_ft_union_singleton]
      intro hc
      rcases hc with hc | hc
      · exact hxΓ hc
      · exact hxA hc
    have h2 := ih c x (hfin.union (Set.finite_singleton _)) hxΓA hxB0
    rw [Set.image_union, Set.image_singleton] at h2
    exact Proof.introI h2
  | elimI h1 h2 ih1 ih2 =>
    intro c x hfin hxΓ hxB
    rename_i A B0 Γ0
    have hS : (Set.free_terms Γ0 ∪ Formula.free_terms A 0 ∪ Formula.free_terms B0 0).Finite :=
      ((Finite_free hfin).union (finite_free _ 0)).union (finite_free _ 0)
    obtain ⟨x', hx'⟩ := exists_fresh_var _ hS
    have hfr := hx' x' (le_refl x')
    have hx'Γ : Term.free x' ∉ Set.free_terms Γ0 :=
      fun hc => hfr (Set.mem_union_left _ (Set.mem_union_left _ hc))
    have hx'A : Term.free x' ∉ Formula.free_terms A 0 :=
      fun hc => hfr (Set.mem_union_left _ (Set.mem_union_right _ hc))
    have hx'B : Term.free x' ∉ Formula.free_terms B0 0 :=
      fun hc => hfr (Set.mem_union_right _ hc)
    have hx'AB : Term.free x' ∉ Formula.free_terms (A →ᵢ B0) 0 := by
      intro hc
      rcases hc with hc | hc
      · exact hx'A hc
      · exact hx'B hc
    have g3 : (Formula.cv c x' 0 '' Γ0) ⊢ Formula.cv c x' 0 B0 :=
      Proof.elimI (ih1 c x' hfin hx'Γ hx'AB) (ih2 c x' hfin hx'Γ hx'A)
    have g4 := swf_proof (a := x) (b := x') g3
    rw [swf_cv_set hxΓ hx'Γ, swf_cv B0 0 hxB hx'B] at g4
    exact g4
  | introA h1 h2 ih1 ih2 =>
    intro c x hfin hxΓ hxB
    rename_i A B0 Γ0 Δ0
    have hfin1 : Γ0.Finite := hfin.subset (Set.subset_union_left _ _)
    have hfin2 : Δ0.Finite := hfin.subset (Set.subset_union_right _ _)
    have hxΓ1 : Term.free x ∉ Set.free_terms Γ0 :=
      fun hc => hxΓ (set_ft_mono (Set.subset_union_left _ _) hc)
    have hxΓ2 : Term.free x ∉ Set.free_terms Δ0 :=
      fun hc => hxΓ (set_ft_mono (Set.subset_union_right _ _) hc)
    have hxA : Term.free x ∉ Formula.free_terms A 0 :=
      fun hc => hxB (Set.mem_union_left _ hc)
    have hxB0 : Term.free x ∉ Formula.free_terms B0 0 :=
      fun hc => hxB (Set.mem_union_right _ hc)
    have g1 := ih1 c x hfin1 hxΓ1 hxA
    have g2 := ih2 c x hfin2 hxΓ2 hxB0
    rw [Set.image_union]
    exact Proof.introA g1 g2
  | elimA1 h ih =>
    intro c x hfin hxΓ hxB
    rename_i A B0 Γ0
    have hS : (Set.free_terms Γ0 ∪ Formula.free_terms A 0 ∪ Formula.free_terms B0 0).Finite :=
      ((Finite_free hfin).union (finite_free _ 0)).union (finite_free _ 0)
    obtain ⟨x', hx'⟩ := exists_fresh_var _ hS
    have hfr := hx' x' (le_refl x')
    have hx'Γ : Term.free x' ∉ Set.free_terms Γ0 :=
      fun hc => hfr (Set.mem_union_left _ (Set.mem_union_left _ hc))
    have hx'A : Term.free x' ∉ Formula.free_terms A 0 :=
      fun hc => hfr (Set.mem_union_left _ (Set.mem_union_right _ hc))
    have hx'B : Term.free x' ∉ Formula.free_terms B0 0 :=
      fun hc => hfr (Set.mem_union_right _ hc)
    have hx'AB : Term.free x' ∉ Formula.free_terms (A ∧ᵢ B0) 0 := by
      intro hc
      rcases hc with hc | hc
      · exact hx'A hc
      · exact hx'B hc
    have g3 : (Formula.cv c x' 0 '' Γ0) ⊢ Formula.cv c x' 0 A :=
      Proof.elimA1 (ih c x' hfin hx'Γ hx'AB)
    have g4 := swf_proof (a := x) (b := x') g3
    rw [swf_cv_set hxΓ hx'Γ, swf_cv A 0 hxB hx'A] at g4
    exact g4
  | elimA2 h ih =>
    intro c x hfin hxΓ hxB
    rename_i A B0 Γ0
    have hS : (Set.free_terms Γ0 ∪ Formula.free_terms A 0 ∪ Formula.free_terms B0 0).Finite :=
      ((Finite_free hfin).union (finite_free _ 0)).union (finite_free _ 0)
    obtain ⟨x', hx'⟩ := exists_fresh_var _ hS
    have hfr := hx' x' (le_refl x')
    have hx'Γ : Term.free x' ∉ Set.free_terms Γ0 :=
      fun hc => hfr (Set.mem_union_left _ (Set.mem_union_left _ hc))
    have hx'A : Term.free x' ∉ Formula.free_terms A 0 :=
      fun hc => hfr (Set.mem_union_left _ (Set.mem_union_right _ hc))
    have hx'B : Term.free x' ∉ Formula.free_terms B0 0 :=
      fun hc => hfr (Set.mem_union_right _ hc)
    have hx'AB : Term.free x' ∉ Formula.free_terms (A ∧ᵢ B0) 0 := by
      intro hc
      rcases hc with hc | hc
      · exact hx'A hc
      · exact hx'B hc
    have g3 : (Formula.cv c x' 0 '' Γ0) ⊢ Formula.cv c x' 0 B0 :=
      Proof.elimA2 (ih c x' hfin hx'Γ hx'AB)
    have g4 := swf_proof (a := x) (b := x') g3
    rw [swf_cv_set hxΓ hx'Γ, swf_cv B0 0 hxB hx'B] at g4
    exact g4
  | introO1 B h ih =>
    intro c x hfin hxΓ hxB
    have hxA : Term.free x ∉ Formula.free_terms _ 0 :=
      fun hc => hxB (Set.mem_union_left _ hc)
    exact Proof.introO1 _ (ih c x hfin hxΓ hxA)
  | introO2 A h ih =>
    intro c x hfin hxΓ hxB
    have hxA : Term.free x ∉ Formula.free_terms _ 0 :=
      fun hc => hxB (Set.mem_union_right _ hc)
    exact Proof.introO2 _ (ih c x hfin hxΓ hxA)
  | elimO h1 h2 h3 ih1 ih2 ih3 =>
    intro c x hfin hxΓ hxB
    rename_i A B0 C0 Γ0
    have hS : (Set.free_terms Γ0 ∪ Formula.free_terms A 0 ∪ Formula.free_terms B0 0
        ∪ Formula.free_terms C0 0).Finite :=
      (((Finite_free hfin).union (finite_free _ 0)).union (finite_free _ 0)).union
        (finite_free _ 0)
    obtain ⟨x', hx'⟩ := exists_fresh_var _ hS
    have hfr := hx' x' (le_refl x')
    have hx'Γ : Term.free x' ∉ Set.free_terms Γ0 :=
      fun hc => hfr (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ hc)))
    have hx'A : Term.free x' ∉ Formula.free_terms A 0 :=
      fun hc => hfr (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ hc)))
    have hx'B : Term.free x' ∉ Formula.free_terms B0 0 :=
      fun hc => hfr (Set.mem_union_left _ (Set.mem_union_right _ hc))
    have hx'C : Term.free x' ∉ Formula.free_terms C0 0 :=
      fun hc => hfr (Set.mem_union_right _ hc)
    have hx'AB : Term.free x' ∉ Formula.free_terms (A ∨ᵢ B0) 0 := by
      intro hc
      rcases hc with hc | hc
      · exact hx'A hc
      · exact hx'B hc
    have hx'ΓA : Term.free x' ∉ Set.free_terms (Γ0 ∪ {A}) := by
      rw [set_ft_union_singleton]
      intro hc
      rcases hc with hc | hc
      · exact hx'Γ hc
      · exact hx'A hc
    have hx'ΓB : Term.free x' ∉ Set.free_terms (Γ0 ∪ {B0}) := by
      rw [set_ft_union_singleton]
      intro hc
      rcases hc with hc | hc
      · exact hx'Γ hc
      · exact hx'B hc
    have g1 := ih1 c x' hfin hx'Γ hx'AB
    have g2 := ih2 c x' (hfin.union (Set.finite_singleton _)) hx'ΓA hx'C
    have g3 := ih3 c x' (hfin.union (Set.finite_singleton _)) hx'ΓB hx'C
    rw [Set.image_union, Set.image_singleton] at g2 g3
    have g5 : (Formula.cv c x' 0 '' Γ0) ⊢ Formula.cv c x' 0 C0 := Proof.elimO g1 g2 g3
    have g6 := swf_proof (a := x) (b := x') g5
    rw [swf_cv_set hxΓ hx'Γ, swf_cv C0 0 hxB hx'C] at g6
    exact g6
  | botE A h ih =>
    intro c x hfin hxΓ hxB
    exact Proof.botE _ (ih c x hfin hxΓ (Set.not_mem_empty _))
  | introF h hy ih =>
    intro c x hfin hxΓ hxB
    rename_i A Γ0 y
    have hS : (Set.free_terms Γ0 ∪ Formula.free_terms A 0
        ∪ Formula.free_terms (∀ᵢ (A.gen y)) 0 ∪ {Term.free y}).Finite :=
      (((Finite_free hfin).union (finite_free _ 0)).union (finite_free _ 0)).union
        (Set.finite_singleton _)
    obtain ⟨x', hx'⟩ := exists_fresh_var _ hS
    have hfr := hx' x' (le_refl x')
    have hx'Γ : Term.free x' ∉ Set.free_terms Γ0 :=
      fun hc => hfr (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ hc)))
    have hx'A : Term.free x' ∉ Formula.free_terms A 0 :=
      fun hc => hfr (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ hc)))
    have hx'F : Term.free x' ∉ Formula.free_terms (∀ᵢ (A.gen y)) 0 :=
      fun hc => hfr (Set.mem_union_left _ (Set.mem_union_right _ hc))
    have hyx' : y ≠ x' := by
      intro hh
      exact hfr (Set.mem_union_right _ (Set.mem_singleton_iff.mpr (by rw [hh])))
    have g1 := ih c x' hfin hx'Γ hx'A
    have heig : Term.free y ∉ Set.free_terms (Formula.cv c x' 0 '' Γ0) :=
      cv_not_mem_set_ft_var hyx' hy
    have g2 := Proof.introF g1 heig
    have g3 : (Formula.cv c x' 0 '' Γ0) ⊢ Formula.cv c x' 0 (∀ᵢ (A.gen y)) := by
      show (Formula.cv c x' 0 '' Γ0) ⊢ (∀ᵢ (Formula.cv c x' 1 (A.gen y)))
      rw [cv_gen hyx']
      exact g2
    have g4 := swf_proof (a := x) (b := x') g3
    rw [swf_cv_set hxΓ hx'Γ, swf_cv _ 0 hxB hx'F] at g4
    exact g4
  | elimF τ h ih =>
    intro c x hfin hxΓ hxB
    rename_i A Γ0
    have hS : (Set.free_terms Γ0 ∪ Formula.free_terms (∀ᵢ A) 0
        ∪ Formula.free_terms (A.inst τ) 0).Finite :=
      ((Finite_free hfin).union (finite_free _ 0)).union (finite_free _ 0)
    obtain ⟨x', hx'⟩ := exists_fresh_var _ hS
    have hfr := hx' x' (le_refl x')
    have hx'Γ : Term.free x' ∉ Set.free_terms Γ0 :=
      fun hc => hfr (Set.mem_union_left _ (Set.mem_union_left _ hc))
    have hx'F : Term.free x' ∉ Formula.free_terms (∀ᵢ A) 0 :=
      fun hc => hfr (Set.mem_union_left _ (Set.mem_union_right _ hc))
    have hx'I : Term.free x' ∉ Formula.free_terms (A.inst τ) 0 :=
      fun hc => hfr (Set.mem_union_right _ hc)
    have g1 := ih c x' hfin hx'Γ hx'F
    have g1' : (Formula.cv c x' 0 '' Γ0) ⊢ (∀ᵢ (Formula.cv c x' 1 A)) := g1
    have g2 := Proof.elimF (Term.cv c x' 0 τ) g1'
    have e1 : Formula.cv c x' 0 (A.inst τ)
        = (Formula.cv c x' 1 A).inst (Term.cv c x' 0 τ) := cv_inst c x' 0 A τ
    rw [← e1] at g2
    have g4 := swf_proof (a := x) (b := x') g2
    rw [swf_cv_set hxΓ hx'Γ, swf_cv _ 0 hxB hx'I] at g4
    exact g4
  | introE τ h ih =>
    intro c x hfin hxΓ hxB
    rename_i A Γ0
    have hS : (Set.free_terms Γ0 ∪ Formula.free_terms (∃ᵢ A) 0
        ∪ Formula.free_terms (A.inst τ) 0).Finite :=
      ((Finite_free hfin).union (finite_free _ 0)).union (finite_free _ 0)
    obtain ⟨x', hx'⟩ := exists_fresh_var _ hS
    have hfr := hx' x' (le_refl x')
    have hx'Γ : Term.free x' ∉ Set.free_terms Γ0 :=
      fun hc => hfr (Set.mem_union_left _ (Set.mem_union_left _ hc))
    have hx'E : Term.free x' ∉ Formula.free_terms (∃ᵢ A) 0 :=
      fun hc => hfr (Set.mem_union_left _ (Set.mem_union_right _ hc))
    have hx'I : Term.free x' ∉ Formula.free_terms (A.inst τ) 0 :=
      fun hc => hfr (Set.mem_union_right _ hc)
    have g1 := ih c x' hfin hx'Γ hx'I
    have e1 : Formula.cv c x' 0 (A.inst τ)
        = (Formula.cv c x' 1 A).inst (Term.cv c x' 0 τ) := cv_inst c x' 0 A τ
    rw [e1] at g1
    have g2 : (Formula.cv c x' 0 '' Γ0) ⊢ Formula.cv c x' 0 (∃ᵢ A) :=
      Proof.introE (Term.cv c x' 0 τ) g1
    have g4 := swf_proof (a := x) (b := x') g2
    rw [swf_cv_set hxΓ hx'Γ, swf_cv _ 0 hxB hx'E] at g4
    exact g4
  | elimE h1 h2 hτΔ hτB hτA ih1 ih2 =>
    intro c x hfin hxΓ hxB
    rename_i A B0 Γ1 Δ1 τ
    have hfin1 : Γ1.Finite := hfin.subset (Set.subset_union_left _ _)
    have hfin2 : Δ1.Finite := hfin.subset (Set.subset_union_right _ _)
    have hS : (Set.free_terms Γ1 ∪ Set.free_terms Δ1 ∪ Formula.free_terms (∃ᵢ A) 0
        ∪ Formula.free_terms B0 0 ∪ Formula.free_terms (A.inst τ) 0 ∪ {τ}).Finite :=
      (((((Finite_free hfin1).union (Finite_free hfin2)).union (finite_free _ 0)).union
        (finite_free _ 0)).union (finite_free _ 0)).union (Set.finite_singleton _)
    obtain ⟨x', hx'⟩ := exists_fresh_var _ hS
    have hfr := hx' x' (le_refl x')
    have hx'Γ1 : Term.free x' ∉ Set.free_terms Γ1 :=
      fun hc => hfr (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
        (Set.mem_union_left _ (Set.mem_union_left _ hc)))))
    have hx'Δ : Term.free x' ∉ Set.free_terms Δ1 :=
      fun hc => hfr (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
        (Set.mem_union_left _ (Set.mem_union_right _ hc)))))
    have hx'E : Term.free x' ∉ Formula.free_terms (∃ᵢ A) 0 :=
      fun hc => hfr (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
        (Set.mem_union_right _ hc))))
    have hx'B : Term.free x' ∉ Formula.free_terms B0 0 :=
      fun hc => hfr (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ hc)))
    have hx'I : Term.free x' ∉ Formula.free_terms (A.inst τ) 0 :=
      fun hc => hfr (Set.mem_union_left _ (Set.mem_union_right _ hc))
    have hx'τ : Term.free x' ∉ ({τ} : Set (Term σ)) :=
      fun hc => hfr (Set.mem_union_right _ hc)
    have g1 := ih1 c x' hfin1 hx'Γ1 hx'E
    have g1' : (Formula.cv c x' 0 '' Γ1) ⊢ (∃ᵢ (Formula.cv c x' 1 A)) := g1
    have hx'ΔI : Term.free x' ∉ Set.free_terms (Δ1 ∪ {A.inst τ}) := by
      rw [set_ft_union_singleton]
      intro hc
      rcases hc with hc | hc
      · exact hx'Δ hc
      · exact hx'I hc
    have g2 := ih2 c x' (hfin2.union (Set.finite_singleton _)) hx'ΔI hx'B
    rw [Set.image_union, Set.image_singleton] at g2
    have e1 : Formula.cv c x' 0 (A.inst τ)
        = (Formula.cv c x' 1 A).inst (Term.cv c x' 0 τ) := cv_inst c x' 0 A τ
    rw [e1] at g2
    have hconds : (Term.cv c x' 0 τ ∉ Set.free_terms (Formula.cv c x' 0 '' Δ1))
        ∧ (Term.cv c x' 0 τ ∉ Formula.free_terms (Formula.cv c x' 0 B0) 0)
        ∧ (Term.cv c x' 0 τ ∉ Formula.free_terms (∃ᵢ (Formula.cv c x' 1 A)) 0) := by
      by_cases hτc : τ = Term.const c
      · rw [hτc] at hτΔ hτB hτA ⊢
        rw [show Term.cv c x' 0 (Term.const c : Term σ) = Term.free x' from cv_const_eq rfl]
        have hB0c : c ∉ B0.consts := fun hc => hτB (const_mem_ft_iff.mpr hc)
        have hAc : c ∉ A.consts := fun hc => hτA (const_mem_ft_iff.mpr hc)
        have hidΔ : Formula.cv c x' 0 '' Δ1 = Δ1 := by
          rw [show Formula.cv c x' 0 '' Δ1 = (fun g => g) '' Δ1 from Set.image_congr
            (fun g hg => cv_id_of_no_const (fun hc =>
              hτΔ (Set.mem_iUnion₂.mpr ⟨g, hg, const_mem_ft_iff.mpr hc⟩)) 0)]
          exact Set.image_id' Δ1
        refine ⟨?_, ?_, ?_⟩
        · rw [hidΔ]
          exact hx'Δ
        · rw [cv_id_of_no_const hB0c 0]
          exact hx'B
        · rw [cv_id_of_no_const hAc 1]
          exact hx'E
      · have hτid : Term.cv c x' 0 τ = τ := by
          cases τ with
          | free n => exact cv_free
          | const q => exact cv_const_ne (fun hh => hτc (congrArg Term.const hh))
        rw [hτid]
        refine ⟨?_, ?_, ?_⟩
        · intro hc
          unfold Set.free_terms at hc
          rw [Set.biUnion_image] at hc
          obtain ⟨g, hg, hmem⟩ := Set.mem_iUnion₂.mp hc
          rcases mem_ft_cv hmem with hh | ⟨hh, _⟩
          · exact hx'τ (Set.mem_singleton_iff.mpr hh.symm)
          · exact hτΔ (Set.mem_iUnion₂.mpr ⟨g, hg, hh⟩)
        · intro hc
          rcases mem_ft_cv hc with hh | ⟨hh, _⟩
          · exact hx'τ (Set.mem_singleton_iff.mpr hh.symm)
          · exact hτB hh
        · intro hc
          have hc' : τ ∈ Formula.free_terms (Formula.cv c x' 1 A) 1 := hc
          rcases mem_ft_cv hc' with hh | ⟨hh, _⟩
          · exact hx'τ (Set.mem_singleton_iff.mpr hh.symm)
          · exact hτA hh
    obtain ⟨hc1, hc2, hc3⟩ := hconds
    have g3 : ((Formula.cv c x' 0 '' Γ1) ∪ (Formula.cv c x' 0 '' Δ1)) ⊢ Formula.cv c x' 0 B0 :=
      Proof.elimE g1' g2 hc1 hc2 hc3
    rw [← Set.image_union] at g3
    have hxU : Term.free x ∉ Set.free_terms (Γ1 ∪ Δ1) := hxΓ
    have hx'U : Term.free x' ∉ Set.free_terms (Γ1 ∪ Δ1) := by
      rw [set_ft_union]
      intro hc
      rcases hc with hc | hc
      · exact hx'Γ1 hc
      · exact hx'Δ hc
    have g4 := swf_proof (a := x) (b := x') g3
    rw [swf_cv_set hxU hx'U, swf_cv B0 0 hxB hx'B] at g4
    exact g4

/- ### Constant generalization -/

private lemma term_inst_gen {x : ℕ} (t : Term σ) (j : ℕ)
    (h : Term.free x ∉ t.free_terms (j+1)) :
    Term.Substitution
        (Term.lift j (Term.down j (Term.Substitution t (Term.free j) (Term.free (x+j+1)))))
        (Term.free (x+j+1)) (Term.free j) = t := by
  cases t with
  | const q => rfl
  | free n =>
    by_cases h1 : n = j
    · have hd : ¬ x + j + 1 < j := by intro hh; linarith
      have hl : ¬ x + j < j := by intro hh; linarith
      rw [subst_free_eq _ h1, down_free_ge hd,
        show x + j + 1 - 1 = x + j from rfl, lift_free_ge hl, subst_free_eq _ rfl, h1]
    · rw [subst_free_ne _ h1]
      by_cases h2 : n < j
      · have hne : ¬ n = x + j + 1 := by intro hh; linarith
        rw [down_free_lt h2, lift_free_lt h2, subst_free_ne _ hne]
      · have hj : j < n := Nat.lt_of_le_of_ne (Nat.le_of_not_lt h2) (Ne.symm h1)
        have hn1 : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos (lt_of_le_of_lt (Nat.zero_le j) hj)
        have hl : ¬ n - 1 < j := by intro hh; linarith
        have hne : ¬ n - 1 + 1 = x + j + 1 := by
          intro hh
          rw [hn1] at hh
          apply h
          have hge : n ≥ j + 1 := hj
          have hsub : n - (j+1) = x := by
            rw [hh, Nat.add_assoc]
            exact Nat.add_sub_cancel x (j+1)
          rw [ft_free_ge hge, hsub]
          rfl
        rw [down_free_ge h2, lift_free_ge hl, subst_free_ne _ hne, hn1]

private lemma inst_gen_aux {x : ℕ} :
    ∀ (A : Formula σ) (j : ℕ), Term.free x ∉ A.free_terms (j+1) →
    (((A.Substitution (Term.free j) (Term.free (x+j+1))).down j).lift j).Substitution
        (Term.free (x+j+1)) (Term.free j) = A := by
  intro A
  induction A with
  | atomic_formula r ts =>
    intro j h
    simp only [Formula.Substitution, Formula.down, Formula.lift]
    congr 1
    funext i
    exact term_inst_gen (ts i) j (fun hc => h (Set.mem_iUnion.mpr ⟨i, hc⟩))
  | conjunction f1 f2 ih1 ih2 =>
    intro j h
    simp only [Formula.Substitution, Formula.down, Formula.lift]
    rw [ih1 j (fun hc => h (Set.mem_union_left _ hc)),
      ih2 j (fun hc => h (Set.mem_union_right _ hc))]
  | disjunction f1 f2 ih1 ih2 =>
    intro j h
    simp only [Formula.Substitution, Formula.down, Formula.lift]
    rw [ih1 j (fun hc => h (Set.mem_union_left _ hc)),
      ih2 j (fun hc => h (Set.mem_union_right _ hc))]
  | implication f1 f2 ih1 ih2 =>
    intro j h
    simp only [Formula.Substitution, Formula.down, Formula.lift]
    rw [ih1 j (fun hc => h (Set.mem_union_left _ hc)),
      ih2 j (fun hc => h (Set.mem_union_right _ hc))]
  | existential_quantification f ih =>
    intro j h
    simp only [Formula.Substitution, Formula.down, Formula.lift]
    have hj : ((Term.free j).lift 0 : Term σ) = Term.free (j+1) :=
      lift_free_ge (Nat.not_lt_zero _)
    have hx : ((Term.free (x+j+1)).lift 0 : Term σ) = Term.free (x+(j+1)+1) :=
      lift_free_ge (Nat.not_lt_zero _)
    rw [hj, hx, ih (j+1) h]
  | universal_quantification f ih =>
    intro j h
    simp only [Formula.Substitution, Formula.down, Formula.lift]
    have hj : ((Term.free j).lift 0 : Term σ) = Term.free (j+1) :=
      lift_free_ge (Nat.not_lt_zero _)
    have hx : ((Term.free (x+j+1)).lift 0 : Term σ) = Term.free (x+(j+1)+1) :=
      lift_free_ge (Nat.not_lt_zero _)
    rw [hj, hx, ih (j+1) h]
  | bottom => intro j h; rfl

/-- Identity needed by `const_gen`: instantiating at a variable that does not
occur and re-abstracting it is the identity. -/
lemma inst_gen_id {x : ℕ} {A : Formula σ}
    (h : Term.free x ∉ A.free_terms 1) :
    (A.inst (Term.free x)).gen x = A := by
  unfold Formula.inst Formula.gen
  have hl : ((Term.free x).lift 0 : Term σ) = Term.free (x+1) :=
    lift_free_ge (Nat.not_lt_zero _)
  rw [hl]
  exact inst_gen_aux A 0 h

/-- If `Γ ⊢ A.inst (const c)` and the constant `c` occurs neither in `Γ` nor in
`A`, then `Γ ⊢ ∀ᵢ A`. -/
theorem const_gen {Γ : Set (Formula σ)} {A : Formula σ} {c : ℕ}
    (h : Γ ⊢ A.inst (Term.const c))
    (hΓ : Term.const c ∉ Set.free_terms Γ) (hA : c ∉ A.consts) :
    Γ ⊢ (∀ᵢ A) := by
  obtain ⟨Γ0, hsub, hprf, hfin⟩ := Finset_proof h
  have hΓ0 : Term.const c ∉ Set.free_terms Γ0 := fun hc => hΓ (set_ft_mono hsub hc)
  have hS : (Set.free_terms Γ0 ∪ Formula.free_terms (A.inst (Term.const c)) 0
      ∪ Formula.free_terms A 1).Finite :=
    ((Finite_free hfin).union (finite_free _ 0)).union (finite_free _ 1)
  obtain ⟨x', hx'⟩ := exists_fresh_var _ hS
  have hfr := hx' x' (le_refl x')
  have hx'Γ0 : Term.free x' ∉ Set.free_terms Γ0 :=
    fun hc => hfr (Set.mem_union_left _ (Set.mem_union_left _ hc))
  have hx'I : Term.free x' ∉ Formula.free_terms (A.inst (Term.const c)) 0 :=
    fun hc => hfr (Set.mem_union_left _ (Set.mem_union_right _ hc))
  have hx'A1 : Term.free x' ∉ Formula.free_terms A 1 :=
    fun hc => hfr (Set.mem_union_right _ hc)
  have g1 := subst_cv hprf c x' hfin hx'Γ0 hx'I
  have hidΓ : Formula.cv c x' 0 '' Γ0 = Γ0 := by
    rw [show Formula.cv c x' 0 '' Γ0 = (fun g => g) '' Γ0 from Set.image_congr
      (fun g hg => cv_id_of_no_const (fun hc =>
        hΓ0 (Set.mem_iUnion₂.mpr ⟨g, hg, const_mem_ft_iff.mpr hc⟩)) 0)]
    exact Set.image_id' Γ0
  have e1 : Formula.cv c x' 0 (A.inst (Term.const c)) = A.inst (Term.free x') := by
    rw [cv_inst c x' 0 A (Term.const c), cv_id_of_no_const hA 1,
      show Term.cv c x' 0 (Term.const c : Term σ) = Term.free x' from cv_const_eq rfl]
  rw [hidΓ, e1] at g1
  have g2 := Proof.introF g1 hx'Γ0
  rw [inst_gen_id hx'A1] at g2
  exact subset_proof g2 hsub

end IFOL
