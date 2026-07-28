/- HISTORICAL RECORD — this file targets the PRE-FIX proof system (commit
455c88e) and NO LONGER COMPILES against the repaired CLM/IFOL.lean: the two
`bad1`/`bad2` derivations below are exactly what the fixed quantifier rules
rule out (elimE now requires τ ∉ FV(∃ᵢA); elimF/introF/introE now use the
cutoff-correct `Formula.inst`/`Formula.gen`). Kept as documentation of why the
rules were changed. To re-check it, `git stash`/checkout the old IFOL.lean. -/
import CLM.IFOL
open IFOL

-- Signature: every relation symbol is binary.
abbrev sig : Signature := ⟨fun _ => 2⟩

-- Q t1 t2  :=  relation 0 applied to (t1, t2)
def Q (t1 t2 : Term sig) : Formula sig :=
  Formula.atomic_formula 0 (fun i => if i.1 = 0 then t1 else t2)

def c : Term sig := Term.const 0

--------------------------------------------------------------------------
-- Counterexample 1: elimE lacks the side condition  τ ∉ FV(∃ᵢ A).
--
--   Γ = {∃x ¬Q(x,c)}   Δ = {∀x Q(x,x)}
-- With witness τ := c (which occurs free in A!) elimE derives Γ∪Δ ⊢ ⊥,
-- but in the model  A=ℕ, Q(a,b) ↔ a=b, c↦0  both hypotheses hold.
--------------------------------------------------------------------------

def exA  : Formula sig := ∃ᵢ ((Q (Term.free 0) c) →ᵢ ⊥)
def allQ : Formula sig := ∀ᵢ (Q (Term.free 0) (Term.free 0))

lemma comp1 :
    (((Q (Term.free 0) c) →ᵢ ⊥).force_Substitution c).force_down
      = ((Q c c) →ᵢ ⊥) := by
  show Formula.implication _ _ = Formula.implication _ _
  congr 1
  show Formula.atomic_formula _ _ = Formula.atomic_formula _ _
  congr 1
  funext i
  fin_cases i <;> rfl

lemma comp2 :
    ((Q (Term.free 0) (Term.free 0)).force_Substitution c).force_down
      = Q c c := by
  show Formula.atomic_formula _ _ = Formula.atomic_formula _ _
  congr 1
  funext i
  fin_cases i <;> rfl

def bad1 : Proof ({exA} ∪ {allQ} : Set (Formula sig)) ⊥ := by
  apply Proof.elimE (A := (Q (Term.free 0) c) →ᵢ ⊥) (τ := c)
  · exact Proof.ref rfl
  · rw [comp1]
    have hall : Proof (({allQ} : Set (Formula sig)) ∪ {(Q c c) →ᵢ ⊥}) allQ :=
      Proof.ref (Or.inl rfl)
    have hQcc := Proof.elimF c hall
    rw [comp2] at hQcc
    exact Proof.elimI (Proof.ref (Or.inr rfl)) hQcc
  · -- c ∉ free_terms {allQ}
    intro hmem
    simp [Set.free_terms, allQ, Q, Formula.free_terms, Term.free_terms] at hmem
  · -- c ∉ (⊥).free_terms 0
    intro hmem
    simp [Formula.free_terms] at hmem

-- The countermodel.
abbrev M0 : model sig :=
  { world := Unit
    W := Set.univ
    A := ℕ
    R := fun _ _ => True
    α := fun _ _ args => args 0 = args 1
    refl := fun _ _ => trivial
    trans := fun _ _ _ _ _ _ _ _ => trivial
    mono := fun _ _ _ _ _ _ _ h => h
    R_closed := fun _ _ _ _ => trivial }

def v0 : Term sig → ℕ
  | Term.free n => n
  | Term.const _ => 0

lemma force_exA (hw : () ∈ M0.W) : Formula.force_form M0 () hw v0 exA := by
  refine ⟨(1:ℕ), ?_⟩
  intro u hR hQ
  have h10 : (1:ℕ) = 0 := hQ
  exact absurd h10 (by decide)

lemma force_allQ (hw : () ∈ M0.W) : Formula.force_form M0 () hw v0 allQ := by
  intro t
  show t = t
  rfl

theorem soundness_false_1 :
    ¬ (∀ (Γ : Set (Formula sig)) (f : Formula sig), (Γ ⊢ f) → (Γ ⊧ f)) := by
  intro h
  have hb := h _ _ bad1 M0 () v0 (Set.mem_univ ()) ?sat
  · exact hb
  case sat =>
    intro f hf
    cases hf with
    | inl hl => simp only [Set.mem_singleton_iff] at hl; subst hl; exact force_exA _
    | inr hr => simp only [Set.mem_singleton_iff] at hr; subst hr; exact force_allQ _

--------------------------------------------------------------------------
-- Counterexample 2: elimF misplaces de Bruijn indices under a nested
-- quantifier (force_Substitution / force_down carry no cutoff).
--
--   Γ = {∀t ∃s Q(s,t)}  ⊢(elimF, τ = free 0)  ∃s Q(s,s)
-- but with Q(a,b) ↔ a = b+1:  ∀t∃s. s=t+1 holds, ∃s. s=s+1 fails.
--------------------------------------------------------------------------

def allex : Formula sig := ∀ᵢ (∃ᵢ (Q (Term.free 0) (Term.free 1)))

lemma comp3 :
    ((∃ᵢ (Q (Term.free 0) (Term.free 1))).force_Substitution (Term.free 0)).force_down
      = (∃ᵢ (Q (Term.free 0) (Term.free 0))) := by
  show Formula.existential_quantification _ = Formula.existential_quantification _
  congr 1
  show Formula.atomic_formula _ _ = Formula.atomic_formula _ _
  congr 1
  funext i
  fin_cases i <;> rfl

def bad2 : Proof ({allex} : Set (Formula sig)) (∃ᵢ (Q (Term.free 0) (Term.free 0))) := by
  have hmem : allex ∈ ({allex} : Set (Formula sig)) := rfl
  have h := Proof.elimF (Term.free 0) (Proof.ref hmem)
  rw [comp3] at h
  exact h

abbrev M1 : model sig :=
  { world := Unit
    W := Set.univ
    A := ℕ
    R := fun _ _ => True
    α := fun _ _ args => args 0 = args 1 + 1
    refl := fun _ _ => trivial
    trans := fun _ _ _ _ _ _ _ _ => trivial
    mono := fun _ _ _ _ _ _ _ h => h
    R_closed := fun _ _ _ _ => trivial }

lemma force_allex (hw : () ∈ M1.W) : Formula.force_form M1 () hw v0 allex := by
  intro t
  refine ⟨t + 1, ?_⟩
  show t + 1 = t + 1
  rfl

theorem soundness_false_2 :
    ¬ (∀ (Γ : Set (Formula sig)) (f : Formula sig), (Γ ⊢ f) → (Γ ⊧ f)) := by
  intro h
  have hb := h _ _ bad2 M1 () v0 (Set.mem_univ ()) ?sat
  · obtain ⟨s, hs⟩ := hb
    exact absurd (hs : s = s + 1) (Nat.ne_of_lt (Nat.lt_succ_self s))
  case sat =>
    intro f hf
    simp only [Set.mem_singleton_iff] at hf
    subst hf
    exact force_allex _

#print axioms soundness_false_1
#print axioms soundness_false_2
