/- Injective constant renamings and the z-translation.

A constant renaming `π : ℕ → ℕ` acts on terms/formulas by `const c ↦ const (π c)`,
leaving free variables (and hence all de Bruijn machinery) untouched.  The key
theorem is `rename_proof`: an injective renaming preserves derivability.

Specializing π to `zc := fun c => 2*c+1` gives the z-translation used by the
Henkin tower: `z_provable_iff : (Γ ⊢ p) ↔ (zc-image Γ ⊢ rn zc p)`.  The forward
direction is `rename_proof zc`; the backward direction picks (via `Finset_proof`)
a finite sub-derivation, bounds its constants by some N, and applies
`rename_proof` with the explicit injection `unz N` that inverts `zc` below N. -/

import CLM.IFOL
import CLM.general
import CLM.completeness
open IFOL
open Set
open Classical

namespace IFOL

variable {σ : Signature}

/- ### The renaming action -/

def Term.rn (π : ℕ → ℕ) : Term σ → Term σ
  | .free n => .free n
  | .const c => .const (π c)

def Formula.rn (π : ℕ → ℕ) : Formula σ → Formula σ
  | .atomic_formula r ts => .atomic_formula r (fun i => (ts i).rn π)
  | .conjunction f1 f2 => .conjunction (f1.rn π) (f2.rn π)
  | .disjunction f1 f2 => .disjunction (f1.rn π) (f2.rn π)
  | .implication f1 f2 => .implication (f1.rn π) (f2.rn π)
  | .existential_quantification f => .existential_quantification (f.rn π)
  | .universal_quantification f => .universal_quantification (f.rn π)
  | .bottom => .bottom

/- ### Constants of a term / formula (no de Bruijn bookkeeping needed) -/

def Term.consts : Term σ → Set ℕ
  | .free _ => ∅
  | .const c => {c}

def Formula.consts : Formula σ → Set ℕ
  | .atomic_formula r ts => ⋃ (i : Fin (σ.arity' r)), (ts i).consts
  | .conjunction f1 f2 => f1.consts ∪ f2.consts
  | .disjunction f1 f2 => f1.consts ∪ f2.consts
  | .implication f1 f2 => f1.consts ∪ f2.consts
  | .existential_quantification f => f.consts
  | .universal_quantification f => f.consts
  | .bottom => ∅

lemma finite_consts (f : Formula σ) : f.consts.Finite := by
  induction f with
  | atomic_formula r ts =>
    apply Set.finite_iUnion
    intro i
    cases ts i with
    | free n => exact Set.finite_empty
    | const c => exact Set.finite_singleton c
  | conjunction f1 f2 ih1 ih2 => exact Set.Finite.union ih1 ih2
  | disjunction f1 f2 ih1 ih2 => exact Set.Finite.union ih1 ih2
  | implication f1 f2 ih1 ih2 => exact Set.Finite.union ih1 ih2
  | existential_quantification f ih => exact ih
  | universal_quantification f ih => exact ih
  | bottom => exact Set.finite_empty

private lemma const_mem_term_ft_iff {t : Term σ} {c b : ℕ} :
    Term.const c ∈ t.free_terms b ↔ c ∈ t.consts := by
  cases t with
  | free z =>
    constructor
    · intro h
      simp only [Term.free_terms] at h
      split at h
      · exact Term.noConfusion h
      · exact absurd h (Set.not_mem_empty _)
    · intro h
      exact absurd h (Set.not_mem_empty _)
  | const z =>
    simp only [Term.free_terms, Term.consts, Set.mem_singleton_iff]
    constructor
    · intro h
      injection h
    · intro h
      rw [h]

/-- Occurrence of a constant in `free_terms` is independent of the bound and
matches `consts`. -/
lemma const_mem_ft_iff {f : Formula σ} {c b : ℕ} :
    Term.const c ∈ f.free_terms b ↔ c ∈ f.consts := by
  induction f generalizing b with
  | atomic_formula r ts =>
    simp only [Formula.free_terms, Formula.consts, Set.mem_iUnion]
    exact exists_congr fun i => const_mem_term_ft_iff
  | conjunction f1 f2 ih1 ih2 =>
    simp only [Formula.free_terms, Formula.consts, Set.mem_union]
    exact or_congr (@ih1 b) (@ih2 b)
  | disjunction f1 f2 ih1 ih2 =>
    simp only [Formula.free_terms, Formula.consts, Set.mem_union]
    exact or_congr (@ih1 b) (@ih2 b)
  | implication f1 f2 ih1 ih2 =>
    simp only [Formula.free_terms, Formula.consts, Set.mem_union]
    exact or_congr (@ih1 b) (@ih2 b)
  | existential_quantification f ih => exact @ih (b+1)
  | universal_quantification f ih => exact @ih (b+1)
  | bottom => exact Iff.rfl

/- ### Basic algebra of `rn` -/

@[simp]
lemma rn_size (π : ℕ → ℕ) (f : Formula σ) : (f.rn π).size = f.size := by
  induction f with
  | atomic_formula r ts => rfl
  | conjunction f1 f2 ih1 ih2 => simp [Formula.rn, ih1, ih2]
  | disjunction f1 f2 ih1 ih2 => simp [Formula.rn, ih1, ih2]
  | implication f1 f2 ih1 ih2 => simp [Formula.rn, ih1, ih2]
  | existential_quantification f ih => simp [Formula.rn, ih]
  | universal_quantification f ih => simp [Formula.rn, ih]
  | bottom => rfl

lemma rn_comp_term (π1 π2 : ℕ → ℕ) (t : Term σ) :
    (t.rn π2).rn π1 = t.rn (π1 ∘ π2) := by
  cases t <;> rfl

lemma rn_comp (π1 π2 : ℕ → ℕ) (f : Formula σ) :
    (f.rn π2).rn π1 = f.rn (π1 ∘ π2) := by
  induction f with
  | atomic_formula r ts =>
    simp only [Formula.rn]
    congr 1
    funext i
    exact rn_comp_term π1 π2 (ts i)
  | conjunction f1 f2 ih1 ih2 => simp only [Formula.rn, ih1, ih2]
  | disjunction f1 f2 ih1 ih2 => simp only [Formula.rn, ih1, ih2]
  | implication f1 f2 ih1 ih2 => simp only [Formula.rn, ih1, ih2]
  | existential_quantification f ih => simp only [Formula.rn, ih]
  | universal_quantification f ih => simp only [Formula.rn, ih]
  | bottom => rfl

lemma rn_congr {π1 π2 : ℕ → ℕ} {f : Formula σ}
    (h : ∀ c ∈ f.consts, π1 c = π2 c) : f.rn π1 = f.rn π2 := by
  induction f with
  | atomic_formula r ts =>
    simp only [Formula.rn]
    congr 1
    funext i
    cases ht : ts i with
    | free n => rfl
    | const c =>
      simp only [Term.rn]
      congr 1
      apply h
      simp only [Formula.consts, Set.mem_iUnion]
      refine ⟨i, ?_⟩
      rw [ht]
      exact rfl
  | conjunction f1 f2 ih1 ih2 =>
    simp only [Formula.rn]
    rw [ih1 (fun c hc => h c (Set.mem_union_left _ hc)),
        ih2 (fun c hc => h c (Set.mem_union_right _ hc))]
  | disjunction f1 f2 ih1 ih2 =>
    simp only [Formula.rn]
    rw [ih1 (fun c hc => h c (Set.mem_union_left _ hc)),
        ih2 (fun c hc => h c (Set.mem_union_right _ hc))]
  | implication f1 f2 ih1 ih2 =>
    simp only [Formula.rn]
    rw [ih1 (fun c hc => h c (Set.mem_union_left _ hc)),
        ih2 (fun c hc => h c (Set.mem_union_right _ hc))]
  | existential_quantification f ih =>
    simp only [Formula.rn]
    rw [ih h]
  | universal_quantification f ih =>
    simp only [Formula.rn]
    rw [ih h]
  | bottom => rfl

@[simp]
lemma rn_id (f : Formula σ) : f.rn (fun c => c) = f := by
  induction f with
  | atomic_formula r ts =>
    simp only [Formula.rn]
    congr 1
    funext i
    cases ts i <;> rfl
  | conjunction f1 f2 ih1 ih2 => simp only [Formula.rn, ih1, ih2]
  | disjunction f1 f2 ih1 ih2 => simp only [Formula.rn, ih1, ih2]
  | implication f1 f2 ih1 ih2 => simp only [Formula.rn, ih1, ih2]
  | existential_quantification f ih => simp only [Formula.rn, ih]
  | universal_quantification f ih => simp only [Formula.rn, ih]
  | bottom => rfl

lemma rn_term_injective {π : ℕ → ℕ} (hπ : Function.Injective π) :
    Function.Injective (Term.rn π : Term σ → Term σ) := by
  intro t1 t2 h
  cases t1 with
  | free n =>
    cases t2 with
    | free m => simpa [Term.rn] using h
    | const c => exact Term.noConfusion h
  | const c =>
    cases t2 with
    | free m => exact Term.noConfusion h
    | const d =>
      simp only [Term.rn, Term.const.injEq] at h ⊢
      exact hπ h

/- ### Commutation with the de Bruijn operations -/

lemma rn_term_lift (π : ℕ → ℕ) (k : ℕ) (t : Term σ) :
    (Term.lift k t).rn π = Term.lift k (t.rn π) := by
  cases t with
  | free n => by_cases h : n < k <;> simp [Term.lift, Term.rn, h]
  | const c => rfl

lemma rn_term_down (π : ℕ → ℕ) (k : ℕ) (t : Term σ) :
    (Term.down k t).rn π = Term.down k (t.rn π) := by
  cases t with
  | free n => by_cases h : n < k <;> simp [Term.down, Term.rn, h]
  | const c => rfl

lemma rn_term_subst {π : ℕ → ℕ} (hπ : Function.Injective π) (s m e : Term σ) :
    (s.Substitution m e).rn π = (s.rn π).Substitution (m.rn π) (e.rn π) := by
  cases s with
  | free n =>
    cases m with
    | free n' => by_cases h : n = n' <;> simp [Term.Substitution, Term.rn, h]
    | const c => rfl
  | const c =>
    cases m with
    | free n' => rfl
    | const c' =>
      by_cases h : c = c'
      · simp [Term.Substitution, Term.rn, h]
      · have h2 : π c ≠ π c' := fun hc => h (hπ hc)
        simp [Term.Substitution, Term.rn, h, h2]

lemma rn_lift (π : ℕ → ℕ) (k : ℕ) (f : Formula σ) :
    (f.lift k).rn π = (f.rn π).lift k := by
  induction f generalizing k with
  | atomic_formula r ts =>
    simp only [Formula.lift, Formula.rn]
    congr 1
    funext i
    exact rn_term_lift π k (ts i)
  | conjunction f1 f2 ih1 ih2 => simp only [Formula.lift, Formula.rn, ih1, ih2]
  | disjunction f1 f2 ih1 ih2 => simp only [Formula.lift, Formula.rn, ih1, ih2]
  | implication f1 f2 ih1 ih2 => simp only [Formula.lift, Formula.rn, ih1, ih2]
  | existential_quantification f ih => simp only [Formula.lift, Formula.rn, ih]
  | universal_quantification f ih => simp only [Formula.lift, Formula.rn, ih]
  | bottom => rfl

lemma rn_down (π : ℕ → ℕ) (k : ℕ) (f : Formula σ) :
    (f.down k).rn π = (f.rn π).down k := by
  induction f generalizing k with
  | atomic_formula r ts =>
    simp only [Formula.down, Formula.rn]
    congr 1
    funext i
    exact rn_term_down π k (ts i)
  | conjunction f1 f2 ih1 ih2 => simp only [Formula.down, Formula.rn, ih1, ih2]
  | disjunction f1 f2 ih1 ih2 => simp only [Formula.down, Formula.rn, ih1, ih2]
  | implication f1 f2 ih1 ih2 => simp only [Formula.down, Formula.rn, ih1, ih2]
  | existential_quantification f ih => simp only [Formula.down, Formula.rn, ih]
  | universal_quantification f ih => simp only [Formula.down, Formula.rn, ih]
  | bottom => rfl

lemma rn_subst {π : ℕ → ℕ} (hπ : Function.Injective π) (f : Formula σ) (m e : Term σ) :
    (f.Substitution m e).rn π = (f.rn π).Substitution (m.rn π) (e.rn π) := by
  induction f generalizing m e with
  | atomic_formula r ts =>
    cases m with
    | free t =>
      simp only [Formula.Substitution, Formula.rn, Term.rn]
      congr 1
      funext i
      exact rn_term_subst hπ (ts i) _ e
    | const t =>
      simp only [Formula.Substitution, Formula.rn, Term.rn]
      congr 1
      funext i
      exact rn_term_subst hπ (ts i) _ e
  | conjunction f1 f2 ih1 ih2 =>
    cases m with
    | free t =>
      simp only [Formula.Substitution, Formula.rn, Term.rn, ih1, ih2]
    | const t =>
      simp only [Formula.Substitution, Formula.rn, Term.rn, ih1, ih2]
  | disjunction f1 f2 ih1 ih2 =>
    cases m with
    | free t =>
      simp only [Formula.Substitution, Formula.rn, Term.rn, ih1, ih2]
    | const t =>
      simp only [Formula.Substitution, Formula.rn, Term.rn, ih1, ih2]
  | implication f1 f2 ih1 ih2 =>
    cases m with
    | free t =>
      simp only [Formula.Substitution, Formula.rn, Term.rn, ih1, ih2]
    | const t =>
      simp only [Formula.Substitution, Formula.rn, Term.rn, ih1, ih2]
  | existential_quantification f ih =>
    cases m with
    | free t =>
      show (∃ᵢ (Formula.rn π (Formula.Substitution f (Term.lift 0 (Term.free t)) (Term.lift 0 e)))) =
        (∃ᵢ (Formula.Substitution (Formula.rn π f) (Term.lift 0 (Term.free t)) (Term.lift 0 (Term.rn π e))))
      rw [ih, rn_term_lift, rn_term_lift]
      rfl
    | const t =>
      simp only [Formula.Substitution, Formula.rn, Term.rn, ih]
  | universal_quantification f ih =>
    cases m with
    | free t =>
      show (∀ᵢ (Formula.rn π (Formula.Substitution f (Term.lift 0 (Term.free t)) (Term.lift 0 e)))) =
        (∀ᵢ (Formula.Substitution (Formula.rn π f) (Term.lift 0 (Term.free t)) (Term.lift 0 (Term.rn π e))))
      rw [ih, rn_term_lift, rn_term_lift]
      rfl
    | const t =>
      simp only [Formula.Substitution, Formula.rn, Term.rn, ih]
  | bottom =>
    cases m with
    | free t => rfl
    | const t => rfl

lemma rn_inst {π : ℕ → ℕ} (hπ : Function.Injective π) (A : Formula σ) (τ : Term σ) :
    (A.inst τ).rn π = (A.rn π).inst (τ.rn π) := by
  unfold Formula.inst
  rw [rn_down, rn_subst hπ, rn_term_lift]
  rfl

lemma rn_gen {π : ℕ → ℕ} (hπ : Function.Injective π) (A : Formula σ) (x : ℕ) :
    (A.gen x).rn π = (A.rn π).gen x := by
  unfold Formula.gen
  rw [rn_subst hπ, rn_lift]
  rfl

/- ### `rn` and free_terms -/

/-- The free terms of a renamed formula are the renamed free terms. -/
lemma rn_free_terms (π : ℕ → ℕ) (f : Formula σ) (b : ℕ) :
    (f.rn π).free_terms b = (Term.rn π) '' (f.free_terms b) := by
  induction f generalizing b with
  | atomic_formula r ts =>
    simp only [Formula.rn, Formula.free_terms, Set.image_iUnion]
    refine congrArg Set.iUnion (funext fun i => ?_)
    cases ts i with
    | free z => by_cases hz : z ≥ b <;> simp [Term.rn, Term.free_terms, hz]
    | const z => simp [Term.rn, Term.free_terms]
  | conjunction f1 f2 ih1 ih2 =>
    simp only [Formula.rn, Formula.free_terms, Set.image_union, ih1, ih2]
  | disjunction f1 f2 ih1 ih2 =>
    simp only [Formula.rn, Formula.free_terms, Set.image_union, ih1, ih2]
  | implication f1 f2 ih1 ih2 =>
    simp only [Formula.rn, Formula.free_terms, Set.image_union, ih1, ih2]
  | existential_quantification f ih =>
    simp only [Formula.rn, Formula.free_terms]
    exact ih (b+1)
  | universal_quantification f ih =>
    simp only [Formula.rn, Formula.free_terms]
    exact ih (b+1)
  | bottom => simp [Formula.rn, Formula.free_terms]

lemma rn_set_free_terms (π : ℕ → ℕ) (Γ : Set (Formula σ)) :
    Set.free_terms ((Formula.rn π) '' Γ) = (Term.rn π) '' (Set.free_terms Γ) := by
  ext t
  simp only [Set.free_terms, Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨g, ⟨f, hf, rfl⟩, ht⟩
    rw [rn_free_terms] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    exact ⟨s, ⟨f, hf, hs⟩, rfl⟩
  · rintro ⟨s, ⟨f, hf, hs⟩, rfl⟩
    refine ⟨f.rn π, ⟨f, hf, rfl⟩, ?_⟩
    rw [rn_free_terms]
    exact ⟨s, hs, rfl⟩

lemma rn_not_mem_ft {π : ℕ → ℕ} (hπ : Function.Injective π) {τ : Term σ}
    {f : Formula σ} {b : ℕ} (h : τ ∉ f.free_terms b) :
    τ.rn π ∉ (f.rn π).free_terms b := by
  rw [rn_free_terms]
  intro hmem
  obtain ⟨s, hs, heq⟩ := hmem
  exact h ((rn_term_injective hπ heq) ▸ hs)

lemma rn_not_mem_set_ft {π : ℕ → ℕ} (hπ : Function.Injective π) {τ : Term σ}
    {Γ : Set (Formula σ)} (h : τ ∉ Set.free_terms Γ) :
    τ.rn π ∉ Set.free_terms ((Formula.rn π) '' Γ) := by
  rw [rn_set_free_terms]
  intro hmem
  obtain ⟨s, hs, heq⟩ := hmem
  exact h ((rn_term_injective hπ heq) ▸ hs)

/-- A free variable occurs in the renamed context iff it occurs in the original. -/
lemma rn_free_var_mem {π : ℕ → ℕ} {x : ℕ} {Γ : Set (Formula σ)} :
    (Term.free x) ∈ Set.free_terms ((Formula.rn π) '' Γ) ↔
      (Term.free x) ∈ Set.free_terms Γ := by
  rw [rn_set_free_terms]
  constructor
  · rintro ⟨s, hs, heq⟩
    cases s with
    | free n =>
      have hn : n = x := by simpa [Term.rn] using heq
      rw [← hn]
      exact hs
    | const c => exact Term.noConfusion heq
  · intro h
    exact ⟨Term.free x, h, rfl⟩

/- ### The main theorem: injective renamings preserve derivability -/

theorem rename_proof {π : ℕ → ℕ} (hπ : Function.Injective π)
    {Γ : Set (Formula σ)} {B : Formula σ} (h : Γ ⊢ B) :
    ((Formula.rn π) '' Γ) ⊢ (B.rn π) := by
  induction h with
  | ref hm => exact Proof.ref (Set.mem_image_of_mem _ hm)
  | introI h ih =>
    apply Proof.introI
    rw [Set.image_union, Set.image_singleton] at ih
    exact ih
  | elimI h1 h2 ih1 ih2 => exact Proof.elimI ih1 ih2
  | introA h1 h2 ih1 ih2 =>
    rw [Set.image_union]
    exact Proof.introA ih1 ih2
  | elimA1 h ih => exact Proof.elimA1 ih
  | elimA2 h ih => exact Proof.elimA2 ih
  | introO1 B h ih => exact Proof.introO1 _ ih
  | introO2 A h ih => exact Proof.introO2 _ ih
  | elimO h1 h2 h3 ih1 ih2 ih3 =>
    apply Proof.elimO ih1
    · rw [Set.image_union, Set.image_singleton] at ih2
      exact ih2
    · rw [Set.image_union, Set.image_singleton] at ih3
      exact ih3
  | botE A h ih => exact Proof.botE _ ih
  | @introF A Γ' x h hx ih =>
    have hgoal : ((∀ᵢ (A.gen x)).rn π) = (∀ᵢ ((A.rn π).gen x)) := by
      simp only [Formula.rn, rn_gen hπ]
    rw [hgoal]
    exact Proof.introF ih (fun hc => hx (rn_free_var_mem.mp hc))
  | elimF τ h ih =>
    have h2 := Proof.elimF (τ.rn π) ih
    rwa [← rn_inst hπ] at h2
  | introE τ h ih =>
    apply Proof.introE (τ.rn π)
    rw [← rn_inst hπ]
    exact ih
  | @elimE A B' Γ' Δ τ h1 h2 hτΔ hτB hτA ih1 ih2 =>
    rw [Set.image_union]
    rw [Set.image_union, Set.image_singleton, rn_inst hπ] at ih2
    exact Proof.elimE ih1 ih2 (rn_not_mem_set_ft hπ hτΔ)
      (rn_not_mem_ft hπ hτB) (rn_not_mem_ft hπ hτA)

/- ### The z-translation and its inverse below a bound -/

def zc : ℕ → ℕ := fun c => 2*c+1

lemma zc_inj : Function.Injective zc := by
  intro a b h
  simp [zc] at h
  exact h

/-- Inverse of `zc` below `N`, extended injectively above. -/
def unz (N : ℕ) : ℕ → ℕ := fun x => if x % 2 = 1 ∧ x < N then x / 2 else N + x

lemma unz_inj (N : ℕ) : Function.Injective (unz N) := by
  intro x y h
  unfold unz at h
  by_cases hx : x % 2 = 1 ∧ x < N <;> by_cases hy : y % 2 = 1 ∧ y < N
  · rw [if_pos hx, if_pos hy] at h
    have hx2 := Nat.div_add_mod x 2
    have hy2 := Nat.div_add_mod y 2
    rw [hx.1] at hx2
    rw [hy.1] at hy2
    rw [← hx2, ← hy2, h]
  · rw [if_pos hx, if_neg hy] at h
    have h1 : x / 2 ≤ x := Nat.div_le_self x 2
    have h2 : x / 2 < N := Nat.lt_of_le_of_lt h1 hx.2
    exfalso
    linarith
  · rw [if_neg hx, if_pos hy] at h
    have h1 : y / 2 ≤ y := Nat.div_le_self y 2
    have h2 : y / 2 < N := Nat.lt_of_le_of_lt h1 hy.2
    exfalso
    linarith
  · rw [if_neg hx, if_neg hy] at h
    exact Nat.add_left_cancel h

lemma unz_zc {c N : ℕ} (h : 2*c+1 < N) : unz N (zc c) = c := by
  have hmod : (2*c+1) % 2 = 1 := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left]
    norm_num
  have hdiv : (2*c+1) / 2 = c := by
    rw [Nat.add_comm, Nat.add_mul_div_left 1 c (by norm_num : 0 < 2)]
    norm_num
  show unz N (2*c+1) = c
  unfold unz
  rw [if_pos ⟨hmod, h⟩]
  exact hdiv

/-- The constants of a renamed formula are the renamed constants. -/
lemma rn_consts (π : ℕ → ℕ) (f : Formula σ) : (f.rn π).consts = π '' f.consts := by
  induction f with
  | atomic_formula r ts =>
    simp only [Formula.rn, Formula.consts, Set.image_iUnion]
    refine congrArg Set.iUnion (funext fun i => ?_)
    cases ts i with
    | free n => simp [Term.rn, Term.consts]
    | const c => simp [Term.rn, Term.consts]
  | conjunction f1 f2 ih1 ih2 =>
    simp only [Formula.rn, Formula.consts, Set.image_union, ih1, ih2]
  | disjunction f1 f2 ih1 ih2 =>
    simp only [Formula.rn, Formula.consts, Set.image_union, ih1, ih2]
  | implication f1 f2 ih1 ih2 =>
    simp only [Formula.rn, Formula.consts, Set.image_union, ih1, ih2]
  | existential_quantification f ih =>
    simp only [Formula.rn, Formula.consts, ih]
  | universal_quantification f ih =>
    simp only [Formula.rn, Formula.consts, ih]
  | bottom => simp [Formula.rn, Formula.consts]

/-- All constants of a z-renamed formula are odd. -/
lemma zc_consts_odd {f : Formula σ} {c : ℕ} (h : c ∈ (f.rn zc).consts) :
    c % 2 = 1 := by
  rw [rn_consts] at h
  obtain ⟨d, _, rfl⟩ := h
  show (2*d+1) % 2 = 1
  rw [Nat.add_comm, Nat.add_mul_mod_self_left]
  norm_num

/-- A z-renamed context contains no even constants: it satisfies `is_inf _ 0`,
i.e. the `std` side condition of the Henkin construction. -/
lemma z_image_std (Γ : Set (Formula σ)) (r : Formula σ) :
    std ((Formula.rn zc) '' Γ) r := by
  intro N _ hc
  simp only [Set.free_terms, Set.mem_iUnion, Set.mem_image] at hc
  obtain ⟨g, ⟨f, _, rfl⟩, hg⟩ := hc
  have h2 := zc_consts_odd (const_mem_ft_iff.mp hg)
  rw [Nat.mul_mod_right] at h2
  exact absurd h2 (by norm_num)

/-- Undo the z-translation below a bound. -/
lemma unz_rn_zc {f : Formula σ} {N : ℕ}
    (h : ∀ c ∈ f.consts, 2*c+1 < N) : (f.rn zc).rn (unz N) = f := by
  rw [rn_comp]
  rw [show f.rn ((unz N) ∘ zc) = f.rn (fun c => c) from
    rn_congr (fun c hc => unz_zc (h c hc))]
  exact rn_id f

/- ### z preserves and reflects provability -/

theorem z_provable_iff (Γ : Set (Formula σ)) (p : Formula σ) :
    (Γ ⊢ p) ↔ (((Formula.rn zc) '' Γ) ⊢ (p.rn zc)) := by
  constructor
  · exact rename_proof zc_inj
  · intro h
    obtain ⟨Γ', hsub, hprf, hfin⟩ := Finset_proof h
    -- Γ' ⊆ zc-image Γ is finite; bound the constants of Γ' ∪ {p.rn zc},
    -- i.e. of the corresponding original formulas, by some N; then apply
    -- rename_proof (unz_inj N) and undo the renaming with unz_rn_zc.
    have hSfin : ((⋃ f ∈ Γ', Formula.consts f) ∪ (p.rn zc).consts).Finite :=
      Set.Finite.union (Set.Finite.biUnion hfin (fun f _ => finite_consts f))
        (finite_consts _)
    obtain ⟨N0, hN0⟩ := hSfin.bddAbove
    have hbound : ∀ x ∈ (⋃ f ∈ Γ', Formula.consts f) ∪ (p.rn zc).consts,
        x < N0 + 1 := fun x hx => Nat.lt_succ_of_le (hN0 hx)
    have h2 := rename_proof (unz_inj (N0 + 1)) hprf
    have hp : ((p.rn zc).rn (unz (N0 + 1))) = p := by
      apply unz_rn_zc
      intro c hc
      have hmem : zc c ∈ (p.rn zc).consts := by
        rw [rn_consts]
        exact Set.mem_image_of_mem _ hc
      exact hbound _ (Set.mem_union_right _ hmem)
    have hΓ : (Formula.rn (unz (N0 + 1))) '' Γ' ⊆ Γ := by
      rintro g' ⟨g, hg, rfl⟩
      obtain ⟨f, hf, rfl⟩ := hsub hg
      have hfz : (f.rn zc).rn (unz (N0 + 1)) = f := by
        apply unz_rn_zc
        intro c hc
        have h1 : zc c ∈ (f.rn zc).consts := by
          rw [rn_consts]
          exact Set.mem_image_of_mem _ hc
        exact hbound _ (Set.mem_union_left _ (Set.mem_biUnion hg h1))
      rw [hfz]
      exact hf
    rw [hp] at h2
    exact subset_proof h2 hΓ

/- ### Forcing a renamed formula (general semantic bridge) -/

lemma force_rn_insert {M0 : model σ} (π : ℕ → ℕ) (v : Term σ → M0.A) (a : M0.A) :
    (fun t => insert_value_function M0 v a (Term.rn π t))
      = insert_value_function M0 (fun t => v (Term.rn π t)) a := by
  funext t
  cases t with
  | free n =>
    cases n with
    | zero => rfl
    | succ m => rfl
  | const c => rfl

/-- Forcing a renamed formula = forcing with the pre-composed valuation.
Holds in any model. -/
lemma force_rn {M0 : model σ} (π : ℕ → ℕ) :
    ∀ (f : Formula σ) (w : M0.world) (hw : w ∈ M0.W) (v : Term σ → M0.A),
    Formula.force_form M0 w hw v (Formula.rn π f) ↔
      Formula.force_form M0 w hw (fun t => v (Term.rn π t)) f := by
  intro f
  induction f with
  | atomic_formula r ts =>
    intro w hw v
    exact Iff.rfl
  | conjunction f1 f2 ih1 ih2 =>
    intro w hw v
    simp only [Formula.rn, Formula.force_form]
    exact and_congr (ih1 w hw v) (ih2 w hw v)
  | disjunction f1 f2 ih1 ih2 =>
    intro w hw v
    simp only [Formula.rn, Formula.force_form]
    exact or_congr (ih1 w hw v) (ih2 w hw v)
  | implication f1 f2 ih1 ih2 =>
    intro w hw v
    simp only [Formula.rn, Formula.force_form]
    constructor
    · intro h u hR hf
      exact (ih2 u (M0.R_closed w u hR hw) v).mp
        (h u hR ((ih1 u (M0.R_closed w u hR hw) v).mpr hf))
    · intro h u hR hf
      exact (ih2 u (M0.R_closed w u hR hw) v).mpr
        (h u hR ((ih1 u (M0.R_closed w u hR hw) v).mp hf))
  | existential_quantification f ih =>
    intro w hw v
    simp only [Formula.rn, Formula.force_form]
    constructor
    · rintro ⟨t, htD, ht⟩
      refine ⟨t, htD, ?_⟩
      have h2 := (ih w hw (insert_value_function M0 v t)).mp ht
      rw [force_rn_insert] at h2
      exact h2
    · rintro ⟨t, htD, ht⟩
      refine ⟨t, htD, ?_⟩
      apply (ih w hw (insert_value_function M0 v t)).mpr
      rw [force_rn_insert]
      exact ht
  | universal_quantification f ih =>
    intro w hw v
    simp only [Formula.rn, Formula.force_form]
    constructor
    · intro h u hR t htD
      have h2 := (ih u (M0.R_closed w u hR hw) (insert_value_function M0 v t)).mp
        (h u hR t htD)
      rw [force_rn_insert] at h2
      exact h2
    · intro h u hR t htD
      apply (ih u (M0.R_closed w u hR hw) (insert_value_function M0 v t)).mpr
      rw [force_rn_insert]
      exact h u hR t htD
  | bottom =>
    intro w hw v
    simp [Formula.rn, Formula.force_form]

end IFOL
