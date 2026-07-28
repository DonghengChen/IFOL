import CLM.IFOL
import CLM.general
open IFOL
open Set
open Classical

variable {σ : Signature}

/- ### Basic simp facts about terms -/

@[simp]
lemma lift_free0 (n : Nat) : Term.lift 0 (Term.free n : Term σ) = Term.free (n+1) := by
  simp [Term.lift]

@[simp]
lemma lift_const0 (c : Nat) : Term.lift 0 (Term.const c : Term σ) = Term.const c := rfl

lemma down_lift0 (e : Term σ) : Term.down 0 (Term.lift 0 e) = e := by
  cases e <;> simp [Term.lift, Term.down]

lemma down_lift_succ {e : Term σ} {d : Nat} (he : Term.down d (Term.lift 0 e) = e) :
    Term.down (d+1) (Term.lift 0 (Term.lift 0 e)) = Term.lift 0 e := by
  cases e with
  | const c => simp [Term.lift, Term.down]
  | free m =>
    simp only [lift_free0, Term.down] at he ⊢
    by_cases h : m + 1 < d
    · exfalso
      simp [h] at he
    · have h2 : ¬ (m + 2 < d + 1) := by
        intro hc
        exact h (Nat.lt_of_succ_lt_succ hc)
      simp [h2, h]

/- ### Valuation combinators and their interaction with `insert_value_function` -/

@[simp]
lemma insert_lift {M : model σ} (v : Term σ → M.A) (a : M.A) (e : Term σ) :
    insert_value_function M v a (Term.lift 0 e) = v e := by
  cases e with
  | free n => simp [insert_value_function]
  | const c => simp [insert_value_function]

/-- Insert value `a` at de Bruijn position `d`, shifting the positions above. -/
def insert_at (M : model σ) (v : Term σ → M.A) (d : Nat) (a : M.A) : Term σ → M.A
  | .free n => if n < d then v (.free n) else if n = d then a else v (.free (n-1))
  | .const c => v (.const c)

lemma insert_at_zero {M : model σ} (v : Term σ → M.A) (a : M.A) :
    insert_at M v 0 a = insert_value_function M v a := by
  funext t
  cases t with
  | free n => simp [insert_at, insert_value_function]
  | const c => rfl

lemma insert_at_succ {M : model σ} (v : Term σ → M.A) (d : Nat) (a t : M.A) :
    insert_at M (insert_value_function M v t) (d+1) a
      = insert_value_function M (insert_at M v d a) t := by
  funext s
  cases s with
  | const c => rfl
  | free n =>
    cases n with
    | zero => simp [insert_at, insert_value_function]
    | succ i =>
      by_cases h1 : i < d
      · have h1' : i + 1 < d + 1 := Nat.succ_lt_succ h1
        simp [insert_at, insert_value_function, h1, h1']
      · by_cases h2 : i = d
        · subst h2
          simp [insert_at, insert_value_function, h1]
        · have h1' : ¬ (i + 1 < d + 1) := fun hc => h1 (Nat.lt_of_succ_lt_succ hc)
          have h2' : ¬ (i + 1 = d + 1) := by simp [h2]
          have hd : d < i := Nat.lt_of_le_of_ne (Nat.le_of_not_lt h1) (Ne.symm h2)
          have hi0 : ¬ (i = 0) := by
            intro h
            subst h
            exact Nat.not_lt_zero d hd
          simp [insert_at, insert_value_function, h1, h2, h1', h2', hi0]

/-- Update the value of the single free variable `x`. -/
def update_free (M : model σ) (v : Term σ → M.A) (x : Nat) (a : M.A) : Term σ → M.A
  | .free n => if n = x then a else v (.free n)
  | .const c => v (.const c)

lemma update_free_succ {M : model σ} (v : Term σ → M.A) (x : Nat) (a t : M.A) :
    update_free M (insert_value_function M v t) (x+1) a
      = insert_value_function M (update_free M v x a) t := by
  funext s
  cases s with
  | const c => rfl
  | free n =>
    cases n with
    | zero => simp [update_free, insert_value_function, Ne.symm (Nat.succ_ne_zero x)]
    | succ i =>
      by_cases h : i = x
      · simp [update_free, insert_value_function, h]
      · simp [update_free, insert_value_function, h]

/-- Forget the value at de Bruijn position `c` (inverse of inserting there). -/
def skip_val (M : model σ) (v : Term σ → M.A) (c : Nat) : Term σ → M.A
  | .free n => if n < c then v (.free n) else v (.free (n+1))
  | .const z => v (.const z)

lemma skip_val_succ {M : model σ} (v : Term σ → M.A) (c : Nat) (t : M.A) :
    skip_val M (insert_value_function M v t) (c+1) = insert_value_function M (skip_val M v c) t := by
  funext s
  cases s with
  | const z => rfl
  | free n =>
    cases n with
    | zero => simp [skip_val, insert_value_function]
    | succ i =>
      by_cases h : i < c
      · have h' : i + 1 < c + 1 := Nat.succ_lt_succ h
        simp [skip_val, insert_value_function, h, h']
      · have h' : ¬ (i + 1 < c + 1) := fun hc => h (Nat.lt_of_succ_lt_succ hc)
        simp [skip_val, insert_value_function, h, h']

/-- Update the value of an arbitrary term `τ` (free variable or constant). -/
def update_term (M : model σ) (v : Term σ → M.A) (τ : Term σ) (a : M.A) : Term σ → M.A :=
  fun t => match τ, t with
  | .free m, .free n => if n = m then a else v (.free n)
  | .const cm, .const cn => if cn = cm then a else v (.const cn)
  | _, _ => v t

@[simp]
lemma update_term_self {M : model σ} (v : Term σ → M.A) (τ : Term σ) (a : M.A) :
    update_term M v τ a τ = a := by
  cases τ <;> simp [update_term]

lemma update_term_ne {M : model σ} (v : Term σ → M.A) (τ : Term σ) (a : M.A)
    {t : Term σ} (h : t ≠ τ) : update_term M v τ a t = v t := by
  cases τ with
  | free m =>
    cases t with
    | free n =>
      have hn : ¬ (n = m) := by
        intro hc
        exact h (by rw [hc])
      simp [update_term, hn]
    | const c => simp [update_term]
  | const cm =>
    cases t with
    | free n => simp [update_term]
    | const cn =>
      have hn : ¬ (cn = cm) := by
        intro hc
        exact h (by rw [hc])
      simp [update_term, hn]

/- ### Membership in `free_terms` -/

lemma mem_ft_free_iff {z b m : Nat} :
    Term.free m ∈ (Term.free z : Term σ).free_terms b ↔ z = m + b := by
  simp only [Term.free_terms, ge_iff_le]
  by_cases h : b ≤ z
  · rw [if_pos h]
    simp only [Set.mem_singleton_iff, Term.free.injEq]
    constructor
    · intro hm
      rw [hm]
      exact (Nat.sub_add_cancel h).symm
    · intro hz
      rw [hz]
      exact (Nat.add_sub_cancel m b).symm
  · rw [if_neg h]
    simp only [Set.mem_empty_iff_false, false_iff]
    intro hz
    exact h (hz ▸ Nat.le_add_left b m)

@[simp]
lemma mem_ft_const_free {z b c : Nat} :
    ¬ ((Term.const c : Term σ) ∈ (Term.free z : Term σ).free_terms b) := by
  simp only [Term.free_terms, ge_iff_le]
  by_cases h : b ≤ z
  · simp [h]
  · simp [h]

@[simp]
lemma mem_ft_const {z b : Nat} {t : Term σ} :
    t ∈ (Term.const z : Term σ).free_terms b ↔ t = Term.const z := by
  simp [Term.free_terms]

lemma term_mem_ft_lift {s t : Term σ} {b : Nat} :
    Term.lift 0 t ∈ s.free_terms b ↔ t ∈ s.free_terms (b+1) := by
  cases s with
  | const z =>
    cases t with
    | free m => simp
    | const c => simp
  | free z =>
    cases t with
    | const c => simp
    | free m =>
      rw [lift_free0, mem_ft_free_iff, mem_ft_free_iff]
      have : m + 1 + b = m + (b + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 b]
      rw [this]

lemma mem_free_terms_lift : ∀ (A : Formula σ) (b : Nat) (t : Term σ),
    Term.lift 0 t ∈ A.free_terms b ↔ t ∈ A.free_terms (b+1) := by
  intro A
  induction A with
  | atomic_formula r ts =>
    intro b t
    simp only [Formula.free_terms, Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, term_mem_ft_lift.mp hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, term_mem_ft_lift.mpr hi⟩
  | conjunction f1 f2 ih1 ih2 =>
    intro b t
    simp only [Formula.free_terms, Set.mem_union]
    rw [ih1, ih2]
  | disjunction f1 f2 ih1 ih2 =>
    intro b t
    simp only [Formula.free_terms, Set.mem_union]
    rw [ih1, ih2]
  | implication f1 f2 ih1 ih2 =>
    intro b t
    simp only [Formula.free_terms, Set.mem_union]
    rw [ih1, ih2]
  | existential_quantification f ih =>
    intro b t
    simp only [Formula.free_terms]
    exact ih (b+1) t
  | universal_quantification f ih =>
    intro b t
    simp only [Formula.free_terms]
    exact ih (b+1) t
  | bottom =>
    intro b t
    simp [Formula.free_terms]

lemma self_mem_ft (t : Term σ) : t ∈ t.free_terms 0 := by
  cases t with
  | free z => simp [Term.free_terms]
  | const z => simp [Term.free_terms]

/- ### The coincidence (agreement) lemma -/

lemma agree_insert {M : model σ} {v1 v2 : Term σ → M.A} {f : Formula σ} (a : M.A)
    (hag : ∀ t, t ∈ f.free_terms 1 → v1 t = v2 t) :
    ∀ t, t ∈ f.free_terms 0 →
      insert_value_function M v1 a t = insert_value_function M v2 a t := by
  intro t ht
  cases t with
  | free n =>
    cases n with
    | zero => simp [insert_value_function]
    | succ i =>
      have hmem : Term.free i ∈ f.free_terms 1 := by
        rw [← mem_free_terms_lift f 0 (Term.free i), lift_free0]
        exact ht
      simp [insert_value_function, hag _ hmem]
  | const c =>
    have hmem : Term.const c ∈ f.free_terms 1 := by
      rw [← mem_free_terms_lift f 0 (Term.const c), lift_const0]
      exact ht
    simp [insert_value_function, hag _ hmem]

lemma force_agree {M : model σ} :
    ∀ (A : Formula σ) (w : M.world) (hw : w ∈ M.W) (v1 v2 : Term σ → M.A),
    (∀ t, t ∈ A.free_terms 0 → v1 t = v2 t) →
    (Formula.force_form M w hw v1 A ↔ Formula.force_form M w hw v2 A) := by
  intro A
  induction A with
  | atomic_formula r ts =>
    intro w hw v1 v2 hag
    simp only [Formula.force_form]
    have harg : (fun i => v1 (ts i)) = fun i => v2 (ts i) := by
      funext i
      apply hag
      simp only [Formula.free_terms, Set.mem_iUnion]
      exact ⟨i, self_mem_ft (ts i)⟩
    rw [harg]
  | conjunction f1 f2 ih1 ih2 =>
    intro w hw v1 v2 hag
    simp only [Formula.force_form]
    have hag1 : ∀ t, t ∈ f1.free_terms 0 → v1 t = v2 t := by
      intro t ht
      exact hag t (by simp only [Formula.free_terms, Set.mem_union]; left; exact ht)
    have hag2 : ∀ t, t ∈ f2.free_terms 0 → v1 t = v2 t := by
      intro t ht
      exact hag t (by simp only [Formula.free_terms, Set.mem_union]; right; exact ht)
    exact and_congr (ih1 w hw v1 v2 hag1) (ih2 w hw v1 v2 hag2)
  | disjunction f1 f2 ih1 ih2 =>
    intro w hw v1 v2 hag
    simp only [Formula.force_form]
    have hag1 : ∀ t, t ∈ f1.free_terms 0 → v1 t = v2 t := by
      intro t ht
      exact hag t (by simp only [Formula.free_terms, Set.mem_union]; left; exact ht)
    have hag2 : ∀ t, t ∈ f2.free_terms 0 → v1 t = v2 t := by
      intro t ht
      exact hag t (by simp only [Formula.free_terms, Set.mem_union]; right; exact ht)
    exact or_congr (ih1 w hw v1 v2 hag1) (ih2 w hw v1 v2 hag2)
  | implication f1 f2 ih1 ih2 =>
    intro w hw v1 v2 hag
    simp only [Formula.force_form]
    have hag1 : ∀ t, t ∈ f1.free_terms 0 → v1 t = v2 t := by
      intro t ht
      exact hag t (by simp only [Formula.free_terms, Set.mem_union]; left; exact ht)
    have hag2 : ∀ t, t ∈ f2.free_terms 0 → v1 t = v2 t := by
      intro t ht
      exact hag t (by simp only [Formula.free_terms, Set.mem_union]; right; exact ht)
    constructor
    · intro h u hR hf
      exact (ih2 u (M.R_closed w u hR hw) v1 v2 hag2).mp
        (h u hR ((ih1 u (M.R_closed w u hR hw) v1 v2 hag1).mpr hf))
    · intro h u hR hf
      exact (ih2 u (M.R_closed w u hR hw) v1 v2 hag2).mpr
        (h u hR ((ih1 u (M.R_closed w u hR hw) v1 v2 hag1).mp hf))
  | existential_quantification f ih =>
    intro w hw v1 v2 hag
    simp only [Formula.force_form]
    have hag' : ∀ t, t ∈ f.free_terms 1 → v1 t = v2 t := by
      intro t ht
      exact hag t (by simp only [Formula.free_terms]; exact ht)
    constructor
    · rintro ⟨t, htD, ht⟩
      exact ⟨t, htD, (ih w hw _ _ (agree_insert t hag')).mp ht⟩
    · rintro ⟨t, htD, ht⟩
      exact ⟨t, htD, (ih w hw _ _ (agree_insert t hag')).mpr ht⟩
  | universal_quantification f ih =>
    intro w hw v1 v2 hag
    simp only [Formula.force_form]
    have hag' : ∀ t, t ∈ f.free_terms 1 → v1 t = v2 t := by
      intro t ht
      exact hag t (by simp only [Formula.free_terms]; exact ht)
    constructor
    · intro h u hR t htD
      exact (ih u (M.R_closed w u hR hw) _ _ (agree_insert t hag')).mp (h u hR t htD)
    · intro h u hR t htD
      exact (ih u (M.R_closed w u hR hw) _ _ (agree_insert t hag')).mpr (h u hR t htD)
  | bottom =>
    intro w hw v1 v2 _
    simp [Formula.force_form]

/- ### Forcing and instantiation: `force (A.inst τ) v ↔ force A (v[0 ↦ v τ])` -/

lemma force_inst_general {M : model σ} :
    ∀ (A : Formula σ) (d : Nat) (e : Term σ) (w : M.world) (hw : w ∈ M.W)
      (v : Term σ → M.A),
    Term.down d (Term.lift 0 e) = e →
    (Formula.force_form M w hw v ((A.Substitution (Term.free d) (Term.lift 0 e)).down d)
      ↔ Formula.force_form M w hw (insert_at M v d (v e)) A) := by
  intro A
  induction A with
  | atomic_formula r ts =>
    intro d e w hw v he
    simp only [Formula.Substitution, Formula.down, Formula.force_form]
    have harg : (fun i => v (Term.down d (Term.Substitution (ts i) (Term.free d) (Term.lift 0 e))))
        = fun i => insert_at M v d (v e) (ts i) := by
      funext i
      cases ts i with
      | const c => simp [Term.Substitution, Term.down, insert_at]
      | free n =>
        by_cases h1 : n < d
        · have h2 : ¬ (n = d) := Nat.ne_of_lt h1
          simp [Term.Substitution, Term.down, insert_at, h1, h2]
        · by_cases h2 : n = d
          · subst h2
            simp [Term.Substitution, insert_at, h1, he]
          · simp [Term.Substitution, Term.down, insert_at, h1, h2]
    rw [harg]
  | conjunction f1 f2 ih1 ih2 =>
    intro d e w hw v he
    simp only [Formula.Substitution, Formula.down, Formula.force_form]
    exact and_congr (ih1 d e w hw v he) (ih2 d e w hw v he)
  | disjunction f1 f2 ih1 ih2 =>
    intro d e w hw v he
    simp only [Formula.Substitution, Formula.down, Formula.force_form]
    exact or_congr (ih1 d e w hw v he) (ih2 d e w hw v he)
  | implication f1 f2 ih1 ih2 =>
    intro d e w hw v he
    simp only [Formula.Substitution, Formula.down, Formula.force_form]
    constructor
    · intro h u hR hf
      exact (ih2 d e u (M.R_closed w u hR hw) v he).mp
        (h u hR ((ih1 d e u (M.R_closed w u hR hw) v he).mpr hf))
    · intro h u hR hf
      exact (ih2 d e u (M.R_closed w u hR hw) v he).mpr
        (h u hR ((ih1 d e u (M.R_closed w u hR hw) v he).mp hf))
  | existential_quantification f ih =>
    intro d e w hw v he
    simp only [Formula.Substitution, Formula.down, Formula.force_form, lift_free0]
    constructor
    · rintro ⟨t, htD, ht⟩
      refine ⟨t, htD, ?_⟩
      have h2 := (ih (d+1) (Term.lift 0 e) w hw (insert_value_function M v t)
        (down_lift_succ he)).mp ht
      rw [insert_lift, insert_at_succ] at h2
      exact h2
    · rintro ⟨t, htD, ht⟩
      refine ⟨t, htD, ?_⟩
      apply (ih (d+1) (Term.lift 0 e) w hw (insert_value_function M v t)
        (down_lift_succ he)).mpr
      rw [insert_lift, insert_at_succ]
      exact ht
  | universal_quantification f ih =>
    intro d e w hw v he
    simp only [Formula.Substitution, Formula.down, Formula.force_form, lift_free0]
    constructor
    · intro h u hR t htD
      have h2 := (ih (d+1) (Term.lift 0 e) u (M.R_closed w u hR hw)
        (insert_value_function M v t) (down_lift_succ he)).mp (h u hR t htD)
      rw [insert_lift, insert_at_succ] at h2
      exact h2
    · intro h u hR t htD
      apply (ih (d+1) (Term.lift 0 e) u (M.R_closed w u hR hw)
        (insert_value_function M v t) (down_lift_succ he)).mpr
      rw [insert_lift, insert_at_succ]
      exact h u hR t htD
  | bottom =>
    intro d e w hw v _
    simp [Formula.Substitution, Formula.down, Formula.force_form]

lemma force_inst {M : model σ} (A : Formula σ) (τ : Term σ) (w : M.world)
    (hw : w ∈ M.W) (v : Term σ → M.A) :
    Formula.force_form M w hw v (A.inst τ)
      ↔ Formula.force_form M w hw (insert_value_function M v (v τ)) A := by
  unfold Formula.inst
  have h := force_inst_general A 0 τ w hw v (down_lift0 τ)
  rw [insert_at_zero] at h
  exact h

/- ### Forcing and substitution of a free variable -/

lemma force_subst_free {M : model σ} :
    ∀ (A : Formula σ) (x : Nat) (e : Term σ) (w : M.world) (hw : w ∈ M.W)
      (v : Term σ → M.A),
    Formula.force_form M w hw v (A.Substitution (Term.free x) e)
      ↔ Formula.force_form M w hw (update_free M v x (v e)) A := by
  intro A
  induction A with
  | atomic_formula r ts =>
    intro x e w hw v
    simp only [Formula.Substitution, Formula.force_form]
    have harg : (fun i => v (Term.Substitution (ts i) (Term.free x) e))
        = fun i => update_free M v x (v e) (ts i) := by
      funext i
      cases ts i with
      | const c => simp [Term.Substitution, update_free]
      | free n =>
        by_cases h : n = x
        · simp [Term.Substitution, update_free, h]
        · simp [Term.Substitution, update_free, h]
    rw [harg]
  | conjunction f1 f2 ih1 ih2 =>
    intro x e w hw v
    simp only [Formula.Substitution, Formula.force_form]
    exact and_congr (ih1 x e w hw v) (ih2 x e w hw v)
  | disjunction f1 f2 ih1 ih2 =>
    intro x e w hw v
    simp only [Formula.Substitution, Formula.force_form]
    exact or_congr (ih1 x e w hw v) (ih2 x e w hw v)
  | implication f1 f2 ih1 ih2 =>
    intro x e w hw v
    simp only [Formula.Substitution, Formula.force_form]
    constructor
    · intro h u hR hf
      exact (ih2 x e u (M.R_closed w u hR hw) v).mp
        (h u hR ((ih1 x e u (M.R_closed w u hR hw) v).mpr hf))
    · intro h u hR hf
      exact (ih2 x e u (M.R_closed w u hR hw) v).mpr
        (h u hR ((ih1 x e u (M.R_closed w u hR hw) v).mp hf))
  | existential_quantification f ih =>
    intro x e w hw v
    simp only [Formula.Substitution, Formula.force_form, lift_free0]
    constructor
    · rintro ⟨t, htD, ht⟩
      refine ⟨t, htD, ?_⟩
      have h2 := (ih (x+1) (Term.lift 0 e) w hw (insert_value_function M v t)).mp ht
      rw [insert_lift, update_free_succ] at h2
      exact h2
    · rintro ⟨t, htD, ht⟩
      refine ⟨t, htD, ?_⟩
      apply (ih (x+1) (Term.lift 0 e) w hw (insert_value_function M v t)).mpr
      rw [insert_lift, update_free_succ]
      exact ht
  | universal_quantification f ih =>
    intro x e w hw v
    simp only [Formula.Substitution, Formula.force_form, lift_free0]
    constructor
    · intro h u hR t htD
      have h2 := (ih (x+1) (Term.lift 0 e) u (M.R_closed w u hR hw)
        (insert_value_function M v t)).mp (h u hR t htD)
      rw [insert_lift, update_free_succ] at h2
      exact h2
    · intro h u hR t htD
      apply (ih (x+1) (Term.lift 0 e) u (M.R_closed w u hR hw)
        (insert_value_function M v t)).mpr
      rw [insert_lift, update_free_succ]
      exact h u hR t htD
  | bottom =>
    intro x e w hw v
    simp [Formula.Substitution, Formula.force_form]

/- ### Forcing and lifting -/

lemma force_lift_iff {M : model σ} :
    ∀ (A : Formula σ) (c : Nat) (w : M.world) (hw : w ∈ M.W) (v : Term σ → M.A),
    Formula.force_form M w hw v (A.lift c)
      ↔ Formula.force_form M w hw (skip_val M v c) A := by
  intro A
  induction A with
  | atomic_formula r ts =>
    intro c w hw v
    simp only [Formula.lift, Formula.force_form]
    have harg : (fun i => v (Term.lift c (ts i))) = fun i => skip_val M v c (ts i) := by
      funext i
      cases ts i with
      | const z => simp [Term.lift, skip_val]
      | free n =>
        by_cases h : n < c
        · simp [Term.lift, skip_val, h]
        · simp [Term.lift, skip_val, h]
    rw [harg]
  | conjunction f1 f2 ih1 ih2 =>
    intro c w hw v
    simp only [Formula.lift, Formula.force_form]
    exact and_congr (ih1 c w hw v) (ih2 c w hw v)
  | disjunction f1 f2 ih1 ih2 =>
    intro c w hw v
    simp only [Formula.lift, Formula.force_form]
    exact or_congr (ih1 c w hw v) (ih2 c w hw v)
  | implication f1 f2 ih1 ih2 =>
    intro c w hw v
    simp only [Formula.lift, Formula.force_form]
    constructor
    · intro h u hR hf
      exact (ih2 c u (M.R_closed w u hR hw) v).mp
        (h u hR ((ih1 c u (M.R_closed w u hR hw) v).mpr hf))
    · intro h u hR hf
      exact (ih2 c u (M.R_closed w u hR hw) v).mpr
        (h u hR ((ih1 c u (M.R_closed w u hR hw) v).mp hf))
  | existential_quantification f ih =>
    intro c w hw v
    simp only [Formula.lift, Formula.force_form]
    constructor
    · rintro ⟨t, htD, ht⟩
      refine ⟨t, htD, ?_⟩
      have h2 := (ih (c+1) w hw (insert_value_function M v t)).mp ht
      rw [skip_val_succ] at h2
      exact h2
    · rintro ⟨t, htD, ht⟩
      refine ⟨t, htD, ?_⟩
      apply (ih (c+1) w hw (insert_value_function M v t)).mpr
      rw [skip_val_succ]
      exact ht
  | universal_quantification f ih =>
    intro c w hw v
    simp only [Formula.lift, Formula.force_form]
    constructor
    · intro h u hR t htD
      have h2 := (ih (c+1) u (M.R_closed w u hR hw) (insert_value_function M v t)).mp
        (h u hR t htD)
      rw [skip_val_succ] at h2
      exact h2
    · intro h u hR t htD
      apply (ih (c+1) u (M.R_closed w u hR hw) (insert_value_function M v t)).mpr
      rw [skip_val_succ]
      exact h u hR t htD
  | bottom =>
    intro c w hw v
    simp [Formula.lift, Formula.force_form]

/- ### Forcing and generalization: `force (A.gen x) (v[0 ↦ t]) ↔ force A (v[x ↦ t])` -/

lemma force_gen {M : model σ} (A : Formula σ) (x : Nat) (w : M.world)
    (hw : w ∈ M.W) (v : Term σ → M.A) (t : M.A) :
    Formula.force_form M w hw (insert_value_function M v t) (A.gen x)
      ↔ Formula.force_form M w hw (update_free M v x t) A := by
  unfold Formula.gen
  rw [force_subst_free, force_lift_iff]
  have hval : skip_val M (update_free M (insert_value_function M v t) (x+1)
      (insert_value_function M v t (Term.free 0))) 0 = update_free M v x t := by
    funext s
    cases s with
    | const c => rfl
    | free n =>
      by_cases h : n = x
      · simp [skip_val, update_free, insert_value_function, h]
      · simp [skip_val, update_free, insert_value_function, h]
  rw [hval]

/- ### Soundness -/

lemma val_in_mono {M : model σ} {w u : M.world} (hw : w ∈ M.W) (hR : M.R w u)
    {v : Term σ → M.A} (hv : val_in M w v) : val_in M u v :=
  fun t => M.D_mono w u hw hR (hv t)

theorem soundness {σ : Signature} (Γ : Set (Formula σ)) (f : Formula σ) :
    (Γ ⊢ f) → (Γ ⊧ f) := fun hp => by
  induction hp with
  | ref hm =>
    intro M w v hw _ hsat
    exact hsat _ hm
  | introI h ih =>
    intro M w v hw hv hsat
    intro u hR hA
    apply ih M u v (M.R_closed w u hR hw) (val_in_mono hw hR hv)
    intro g hg
    cases hg with
    | inl hgΓ =>
      exact Formula.mono_proof M w u hR g hw v (hsat g hgΓ)
    | inr hgA =>
      simp only [Set.mem_singleton_iff] at hgA
      rw [hgA]
      exact hA
  | elimI h1 h2 ih1 ih2 =>
    intro M w v hw hv hsat
    exact ih1 M w v hw hv hsat w (M.refl w hw) (ih2 M w v hw hv hsat)
  | introA h1 h2 ih1 ih2 =>
    intro M w v hw hv hsat
    exact ⟨ih1 M w v hw hv (fun g hg => hsat g (Or.inl hg)),
           ih2 M w v hw hv (fun g hg => hsat g (Or.inr hg))⟩
  | elimA1 h ih =>
    intro M w v hw hv hsat
    exact (ih M w v hw hv hsat).left
  | elimA2 h ih =>
    intro M w v hw hv hsat
    exact (ih M w v hw hv hsat).right
  | introO1 B h ih =>
    intro M w v hw hv hsat
    exact Or.inl (ih M w v hw hv hsat)
  | introO2 A h ih =>
    intro M w v hw hv hsat
    exact Or.inr (ih M w v hw hv hsat)
  | elimO h1 h2 h3 ih1 ih2 ih3 =>
    intro M w v hw hv hsat
    cases ih1 M w v hw hv hsat with
    | inl hA =>
      apply ih2 M w v hw hv
      intro g hg
      cases hg with
      | inl hgΓ => exact hsat g hgΓ
      | inr hgA =>
        simp only [Set.mem_singleton_iff] at hgA
        rw [hgA]
        exact hA
    | inr hB =>
      apply ih3 M w v hw hv
      intro g hg
      cases hg with
      | inl hgΓ => exact hsat g hgΓ
      | inr hgB =>
        simp only [Set.mem_singleton_iff] at hgB
        rw [hgB]
        exact hB
  | botE A h ih =>
    intro M w v hw hv hsat
    exact (ih M w v hw hv hsat).elim
  | introF h hx ih =>
    rename_i A1 Γ1 x
    intro M w v hw hv hsat
    intro u hR t htD
    have hu : u ∈ M.W := M.R_closed w u hR hw
    rw [force_gen]
    have hv' : val_in M u (update_free M v x t) := by
      intro s
      cases s with
      | const c => exact M.D_mono w u hw hR (hv (Term.const c))
      | free n =>
        by_cases hn : n = x
        · simp only [update_free, if_pos hn]
          exact htD
        · simp only [update_free, if_neg hn]
          exact M.D_mono w u hw hR (hv (Term.free n))
    apply ih M u (update_free M v x t) hu hv'
    intro g hg
    apply (force_agree g u hu v (update_free M v x t) ?_).mp
      (Formula.mono_proof M w u hR g hw v (hsat g hg))
    intro s hs
    cases s with
    | const c => rfl
    | free n =>
      by_cases hn : n = x
      · exfalso
        apply hx
        subst hn
        simp only [Set.free_terms, Set.mem_iUnion]
        exact ⟨g, hg, hs⟩
      · simp [update_free, hn]
  | elimF τ h ih =>
    intro M w v hw hv hsat
    rw [force_inst]
    exact ih M w v hw hv hsat w (M.refl w hw) (v τ) (hv τ)
  | introE τ h ih =>
    intro M w v hw hv hsat
    have h1 := ih M w v hw hv hsat
    rw [force_inst] at h1
    exact ⟨v τ, hv τ, h1⟩
  | elimE h1 h2 hτΔ hτB hτA ih1 ih2 =>
    rename_i A B Γ' Δ τ
    intro M w v hw hv hsat
    obtain ⟨a, haD, ha⟩ := ih1 M w v hw hv (fun g hg => hsat g (Or.inl hg))
    have hagree : ∀ (g : Formula σ), τ ∉ g.free_terms 0 →
        ∀ s, s ∈ g.free_terms 0 → v s = update_term M v τ a s := by
      intro g hτg s hs
      have hne : s ≠ τ := fun hc => hτg (hc ▸ hs)
      exact (update_term_ne v τ a hne).symm
    have hAinst : Formula.force_form M w hw (update_term M v τ a) (A.inst τ) := by
      rw [force_inst, update_term_self]
      apply (force_agree A w hw (insert_value_function M v a)
        (insert_value_function M (update_term M v τ a) a) ?_).mp ha
      apply agree_insert
      intro s hs
      have hne : s ≠ τ := by
        intro hc
        apply hτA
        subst hc
        simp only [Formula.free_terms]
        exact hs
      exact (update_term_ne v τ a hne).symm
    have hv' : val_in M w (update_term M v τ a) := by
      intro s
      by_cases hs : s = τ
      · rw [hs, update_term_self]
        exact haD
      · rw [update_term_ne v τ a hs]
        exact hv s
    have hB := ih2 M w (update_term M v τ a) hw hv' ?_
    · exact (force_agree B w hw v (update_term M v τ a) (hagree B hτB)).mpr hB
    · intro g hg
      cases hg with
      | inl hgΔ =>
        have hτg : τ ∉ g.free_terms 0 := by
          intro hc
          apply hτΔ
          simp only [Set.free_terms, Set.mem_iUnion]
          exact ⟨g, hgΔ, hc⟩
        exact (force_agree g w hw v (update_term M v τ a) (hagree g hτg)).mp
          (hsat g (Or.inr hgΔ))
      | inr hgi =>
        simp only [Set.mem_singleton_iff] at hgi
        rw [hgi]
        exact hAinst
