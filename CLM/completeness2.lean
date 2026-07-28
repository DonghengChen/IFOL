/- Completeness of IFOL for expanding-domain Kripke semantics.

Canonical model with a language tower:
- worlds are pairs `(Δ, k)` of a prime consistent theory and a *level* `k`;
- `R (Δ,k) (Θ,l)` holds iff `k ≤ l` and the `(l-k)`-fold z-translation of `Δ`
  (constants `c ↦ 2c+1`, iterated) is contained in `Θ`;
- domain elements are pairs `(j, m) : ℕ × ℕ` — "the term `det m`, born at
  level `j`" — with `D (Δ,k) = {a | a.1 ≤ k}`: the element `(j,m)` is denoted
  at level `k ≥ j` by the term `znT (k-j) (det m)`  (`tmc`);
- the atomic valuation reads the (level-adjusted) atom off the theory.

The point of the tower: to build a successor world of `(Δ,k)` we z-translate
`Δ` — making every constant odd — and run the Henkin construction `prime`,
whose witnesses use only fresh EVEN constants.  This is what the odd/even
recycling was designed for: each level reuses the single ℕ-indexed constant
pool.  The two directions of the truth lemma that need fresh constants
(→ᵢ and ∀ᵢ, force → provable) both step one level up.

The final theorem here is completeness under `std Γ p` (Γ has no even
constants); `z_translate.lean` removes that hypothesis. -/

import CLM.completeness
import CLM.bijection
import CLM.soundness
import CLM.rename
import CLM.cv
open IFOL
open Set
open Classical

variable {σ : Signature}

def is_consist (Γ : Set (Formula σ)) := ¬ (Γ ⊢ ⊥)

lemma consist_of_not_prf {Γ : Set (Formula σ)} {p : Formula σ} :
    ¬ (Γ ⊢ p) → is_consist Γ := fun x y => x (Proof.botE p y)

/- ### Iterated z-translation -/

def zcn : ℕ → ℕ → ℕ
  | 0 => fun c => c
  | n+1 => fun c => zc (zcn n c)

lemma zcn_inj (n : ℕ) : Function.Injective (zcn n) := by
  induction n with
  | zero => exact fun a b h => h
  | succ n ih => exact fun a b h => ih (zc_inj h)

lemma zcn_add (m n : ℕ) : ∀ c, zcn (m+n) c = zcn m (zcn n c) := by
  induction m with
  | zero =>
    intro c
    rw [Nat.zero_add]
    rfl
  | succ m ih =>
    intro c
    rw [Nat.succ_add]
    show zc (zcn (m+n) c) = zc (zcn m (zcn n c))
    rw [ih c]

def znT (n : ℕ) (t : Term σ) : Term σ := Term.rn (zcn n) t
def znF (n : ℕ) (f : Formula σ) : Formula σ := Formula.rn (zcn n) f

lemma znF_one_eq : (znF 1 : Formula σ → Formula σ) = Formula.rn zc := by
  funext f
  exact rn_congr (fun c _ => rfl)

@[simp]
lemma znF_size (n : ℕ) (f : Formula σ) : (znF n f).size = f.size := rn_size _ f

lemma znT_add (m n : ℕ) (t : Term σ) : znT m (znT n t) = znT (m+n) t := by
  unfold znT
  rw [rn_comp_term]
  cases t with
  | free k => rfl
  | const c =>
    show Term.const (zcn m (zcn n c)) = Term.const (zcn (m+n) c)
    rw [zcn_add]

lemma znF_add (m n : ℕ) (f : Formula σ) : znF m (znF n f) = znF (m+n) f := by
  unfold znF
  rw [rn_comp]
  exact rn_congr (fun c _ => (zcn_add m n c).symm)

@[simp] lemma znF_zero (f : Formula σ) : znF 0 f = f := rn_id f
@[simp] lemma znT_free (n m : ℕ) : znT n (Term.free m : Term σ) = Term.free m := rfl
@[simp] lemma znF_imp (n : ℕ) (f1 f2 : Formula σ) :
    znF n (f1 →ᵢ f2) = ((znF n f1) →ᵢ (znF n f2)) := rfl
@[simp] lemma znF_and (n : ℕ) (f1 f2 : Formula σ) :
    znF n (f1 ∧ᵢ f2) = ((znF n f1) ∧ᵢ (znF n f2)) := rfl
@[simp] lemma znF_or (n : ℕ) (f1 f2 : Formula σ) :
    znF n (f1 ∨ᵢ f2) = ((znF n f1) ∨ᵢ (znF n f2)) := rfl
@[simp] lemma znF_ex (n : ℕ) (f : Formula σ) : znF n (∃ᵢ f) = (∃ᵢ (znF n f)) := rfl
@[simp] lemma znF_all (n : ℕ) (f : Formula σ) : znF n (∀ᵢ f) = (∀ᵢ (znF n f)) := rfl
@[simp] lemma znF_bot (n : ℕ) : znF n (Formula.bottom : Formula σ) = Formula.bottom := rfl

lemma zn_provable {m : ℕ} {Γ : Set (Formula σ)} {p : Formula σ} (h : Γ ⊢ p) :
    ((znF m) '' Γ) ⊢ (znF m p) := rename_proof (zcn_inj m) h

lemma znF_inst (m : ℕ) (A : Formula σ) (τ : Term σ) :
    znF m (A.inst τ) = (znF m A).inst (znT m τ) := rn_inst (zcn_inj m) A τ

/- ### The canonical model -/

def worlds : Set (Set (Formula σ) × ℕ) := {w | is_consist w.1 ∧ is_prime w.1}

/-- The term denoting element `(j,m)` at level `k` (meaningful for `j ≤ k`). -/
def tmc (k : ℕ) (a : ℕ × ℕ) : Term σ := znT (k - a.1) (det a.2)

@[simp]
lemma znT_zero (t : Term σ) : znT 0 t = t := by cases t <;> rfl

lemma tmc_shift {a : ℕ × ℕ} {k l : ℕ} (hak : a.1 ≤ k) (hkl : k ≤ l) :
    (tmc l a : Term σ) = znT (l - k) (tmc k a) := by
  unfold tmc
  rw [znT_add]
  congr 1
  exact (tsub_add_tsub_cancel hkl hak).symm

lemma tmc_valL (k : ℕ) (τ : Term σ) : tmc k ((k, ent τ)) = τ := by
  unfold tmc
  simp only [Nat.sub_self]
  rw [znT_zero, de_bij]

namespace canonical

@[simp]
def M {σ : Signature} : model σ where
  world := Set (Formula σ) × ℕ
  W := worlds
  A := ℕ × ℕ
  D := fun w => {a | a.1 ≤ w.2}
  R := fun w u => (w.2 ≤ u.2 ∧ (znF (u.2 - w.2)) '' w.1 ⊆ u.1) ∧ u ∈ worlds
  α := fun w r map =>
    (∀ i, (map i).1 ≤ w.2) ∧
      (@Formula.atomic_formula σ r (fun i => tmc w.2 (map i))) ∈ w.1
  refl := by
    intro w hw
    refine ⟨⟨le_refl _, ?_⟩, hw⟩
    intro f hf
    rcases hf with ⟨g, hg, hfg⟩
    rw [← hfg]
    rw [Nat.sub_self]
    rw [znF_zero]
    exact hg
  trans := by
    intro w hw v hv u hu h1 h2
    refine ⟨⟨le_trans h1.1.1 h2.1.1, ?_⟩, hu⟩
    intro f hf
    rcases hf with ⟨g, hg, hfg⟩
    have h3 : znF (u.2 - v.2) (znF (v.2 - w.2) g) = f := by
      rw [znF_add, ← hfg]
      congr 1
      exact tsub_add_tsub_cancel h2.1.1 h1.1.1
    rw [← h3]
    apply h2.1.2
    exact ⟨znF (v.2 - w.2) g, h1.1.2 ⟨g, hg, rfl⟩, rfl⟩
  mono := by
    intro u v hu hv r args h hα
    refine ⟨fun i => le_trans (hα.1 i) h.1.1, ?_⟩
    have h2 := h.1.2 ⟨_, hα.2, rfl⟩
    have h3 : znF (v.2 - u.2) ((Formula.atomic_formula r (fun i => tmc u.2 (args i))))
        = (Formula.atomic_formula r (fun i => tmc v.2 (args i))) := by
      show Formula.rn (zcn (v.2 - u.2)) _ = _
      simp only [Formula.rn]
      congr 1
      funext i
      show znT (v.2 - u.2) (tmc u.2 (args i)) = tmc v.2 (args i)
      exact (tmc_shift (hα.1 i) h.1.1).symm
    rw [h3] at h2
    exact h2
  R_closed := by
    intro u v h _
    exact h.2
  D_mono := by
    intro u v _ h a ha
    exact le_trans (show a.1 ≤ u.2 from ha) h.1.1

/-- Level-`k` valuation: every term denotes itself, born at level `k`. -/
def valL (k : ℕ) : Term σ → (ℕ × ℕ) := fun τ => (k, ent τ)

lemma closed {p : Formula σ} {w : Set (Formula σ) × ℕ} (h0 : w ∈ (@M σ).W) :
    (p ∈ w.1) ↔ (w.1 ⊢ p) := by
  constructor
  · exact fun h => Proof.ref h
  · intro h
    exact h0.2.1 p h

/- ### Semantic bridges (`force_rn` is provided by `CLM/rename.lean`) -/

/-- In the canonical model, forcing only depends on the level-adjusted terms
denoted by the valuation (and on the valuation landing in the domain). -/
lemma force_tm_agree :
    ∀ (f : Formula σ) (w : Set (Formula σ) × ℕ) (h : w ∈ (@M σ).W)
      (v1 v2 : Term σ → ℕ × ℕ),
    (∀ τ, (v1 τ).1 ≤ w.2 ∧ (v2 τ).1 ≤ w.2 ∧ tmc w.2 (v1 τ) = (tmc w.2 (v2 τ) : Term σ)) →
    (Formula.force_form M w h v1 f ↔ Formula.force_form M w h v2 f) := by
  intro f
  induction f with
  | atomic_formula r ts =>
    intro w h v1 v2 hag
    constructor
    · rintro ⟨hlev, hmem⟩
      refine ⟨fun i => (hag (ts i)).2.1, ?_⟩
      have harg : (fun i => (tmc w.2 (v2 (ts i)) : Term σ))
          = (fun i => tmc w.2 (v1 (ts i))) :=
        funext fun i => ((hag (ts i)).2.2).symm
      rw [harg]
      exact hmem
    · rintro ⟨hlev, hmem⟩
      refine ⟨fun i => (hag (ts i)).1, ?_⟩
      have harg : (fun i => (tmc w.2 (v1 (ts i)) : Term σ))
          = (fun i => tmc w.2 (v2 (ts i))) :=
        funext fun i => (hag (ts i)).2.2
      rw [harg]
      exact hmem
  | conjunction f1 f2 ih1 ih2 =>
    intro w h v1 v2 hag
    exact and_congr (ih1 w h v1 v2 hag) (ih2 w h v1 v2 hag)
  | disjunction f1 f2 ih1 ih2 =>
    intro w h v1 v2 hag
    exact or_congr (ih1 w h v1 v2 hag) (ih2 w h v1 v2 hag)
  | implication f1 f2 ih1 ih2 =>
    intro w h v1 v2 hag
    have hagU : ∀ (u : Set (Formula σ) × ℕ), (@M σ).R w u →
        (∀ τ, (v1 τ).1 ≤ u.2 ∧ (v2 τ).1 ≤ u.2 ∧
          tmc u.2 (v1 τ) = (tmc u.2 (v2 τ) : Term σ)) := by
      intro u hR τ
      obtain ⟨h1, h2, h3⟩ := hag τ
      refine ⟨le_trans h1 hR.1.1, le_trans h2 hR.1.1, ?_⟩
      rw [tmc_shift h1 hR.1.1, tmc_shift h2 hR.1.1, h3]
    constructor
    · intro hf u hR hf1
      exact (ih2 u ((@M σ).R_closed w u hR h) v1 v2 (hagU u hR)).mp
        (hf u hR ((ih1 u ((@M σ).R_closed w u hR h) v1 v2 (hagU u hR)).mpr hf1))
    · intro hf u hR hf1
      exact (ih2 u ((@M σ).R_closed w u hR h) v1 v2 (hagU u hR)).mpr
        (hf u hR ((ih1 u ((@M σ).R_closed w u hR h) v1 v2 (hagU u hR)).mp hf1))
  | existential_quantification f ih =>
    intro w h v1 v2 hag
    constructor
    · rintro ⟨t, htD, hf⟩
      refine ⟨t, htD, ?_⟩
      apply (ih w h _ _ ?_).mp hf
      intro τ
      cases τ with
      | const c => exact hag (Term.const c)
      | free n =>
        cases n with
        | zero => exact ⟨htD, htD, rfl⟩
        | succ m => exact hag (Term.free m)
    · rintro ⟨t, htD, hf⟩
      refine ⟨t, htD, ?_⟩
      apply (ih w h _ _ ?_).mpr hf
      intro τ
      cases τ with
      | const c => exact hag (Term.const c)
      | free n =>
        cases n with
        | zero => exact ⟨htD, htD, rfl⟩
        | succ m => exact hag (Term.free m)
  | universal_quantification f ih =>
    intro w h v1 v2 hag
    have hagU : ∀ (u : Set (Formula σ) × ℕ), (@M σ).R w u → ∀ (t : ℕ × ℕ), t ∈ (@M σ).D u →
        (∀ τ, (insert_value_function (@M σ) v1 t τ).1 ≤ u.2 ∧
          (insert_value_function (@M σ) v2 t τ).1 ≤ u.2 ∧
          tmc u.2 (insert_value_function (@M σ) v1 t τ)
            = (tmc u.2 (insert_value_function (@M σ) v2 t τ) : Term σ)) := by
      intro u hR t htD τ
      cases τ with
      | const c =>
        obtain ⟨h1, h2, h3⟩ := hag (Term.const c)
        have h4 : tmc u.2 (v1 (Term.const c)) = (tmc u.2 (v2 (Term.const c)) : Term σ) := by
          rw [tmc_shift h1 hR.1.1, tmc_shift h2 hR.1.1, h3]
        exact ⟨le_trans h1 hR.1.1, le_trans h2 hR.1.1, h4⟩
      | free n =>
        cases n with
        | zero => exact ⟨htD, htD, rfl⟩
        | succ m =>
          obtain ⟨h1, h2, h3⟩ := hag (Term.free m)
          have h4 : tmc u.2 (v1 (Term.free m)) = (tmc u.2 (v2 (Term.free m)) : Term σ) := by
            rw [tmc_shift h1 hR.1.1, tmc_shift h2 hR.1.1, h3]
          exact ⟨le_trans h1 hR.1.1, le_trans h2 hR.1.1, h4⟩
    constructor
    · intro hf u hR t htD
      exact (ih u ((@M σ).R_closed w u hR h) _ _ (hagU u hR t htD)).mp (hf u hR t htD)
    · intro hf u hR t htD
      exact (ih u ((@M σ).R_closed w u hR h) _ _ (hagU u hR t htD)).mpr (hf u hR t htD)
  | bottom =>
    intro w h v1 v2 _
    exact Iff.rfl

/-- Shift a forcing statement across levels: at a world of level `u.2`,
evaluating `f` with the level-`k` valuation (`k ≤ u.2`) is the same as
evaluating the `(u.2-k)`-fold z-translation of `f` with the native valuation. -/
lemma force_shift {f : Formula σ} {u : Set (Formula σ) × ℕ} {k : ℕ}
    (h : u ∈ (@M σ).W) (hkl : k ≤ u.2) :
    Formula.force_form M u h (valL k) f ↔
      Formula.force_form M u h (valL u.2) (znF (u.2 - k) f) := by
  unfold znF
  rw [force_rn]
  apply force_tm_agree
  intro τ
  refine ⟨hkl, le_refl u.2, ?_⟩
  show tmc u.2 ((k, ent τ)) = tmc u.2 ((u.2, ent (Term.rn (zcn (u.2 - k)) τ)))
  rw [tmc_valL]
  show znT (u.2 - k) (det (ent τ)) = Term.rn (zcn (u.2 - k)) τ
  rw [de_bij]
  rfl

/-- The universal bridge: an element `t` of the domain at a future world `u`,
inserted into the level-`k` valuation, forces the body `f` iff the native
valuation forces the level-adjusted instance of `f` at the term `tmc u.2 t`
denoting `t`. -/
lemma bridge_univ {u : Set (Formula σ) × ℕ} (hu : u ∈ (@M σ).W) {k : ℕ}
    (hk : k ≤ u.2) (t : ℕ × ℕ) (htD : t.1 ≤ u.2) (f : Formula σ) :
    Formula.force_form M u hu (insert_value_function (@M σ) (valL k) t) f ↔
      Formula.force_form M u hu (valL u.2) ((znF (u.2 - k) f).inst (tmc u.2 t)) := by
  rw [force_inst]
  unfold znF
  rw [force_rn]
  apply force_tm_agree
  intro s
  cases s with
  | free n =>
    cases n with
    | zero =>
      refine ⟨htD, le_refl u.2, ?_⟩
      have h5 : (tmc u.2 ((u.2, ent (tmc u.2 t))) : Term σ) = tmc u.2 t :=
        tmc_valL u.2 (tmc u.2 t)
      exact h5.symm
    | succ m =>
      refine ⟨hk, le_refl u.2, ?_⟩
      have h5 : (tmc u.2 ((k, ent (Term.free m : Term σ))) : Term σ) = Term.free m := by
        unfold tmc
        show znT (u.2 - k) (det (ent (Term.free m : Term σ))) = Term.free m
        rw [de_bij]
        rfl
      have h6 : (tmc u.2 ((u.2, ent (Term.free m : Term σ))) : Term σ) = Term.free m :=
        tmc_valL u.2 (Term.free m)
      exact h5.trans h6.symm
  | const c =>
    refine ⟨hk, le_refl u.2, ?_⟩
    have h5 : (tmc u.2 ((k, ent (Term.const c : Term σ))) : Term σ)
        = Term.const (zcn (u.2 - k) c) := by
      unfold tmc
      show znT (u.2 - k) (det (ent (Term.const c : Term σ))) = Term.const (zcn (u.2 - k) c)
      rw [de_bij]
      rfl
    have h6 : (tmc u.2 ((u.2, ent (Term.const (zcn (u.2 - k) c) : Term σ))) : Term σ)
        = Term.const (zcn (u.2 - k) c) :=
      tmc_valL u.2 (Term.const (zcn (u.2 - k) c))
    exact h5.trans h6.symm

/- ### Freshness of even constants for z-images -/

lemma no_even_in_z_image (Γ : Set (Formula σ)) (m : ℕ) :
    Term.const (2*m) ∉ Set.free_terms ((znF 1) '' Γ) := by
  rw [znF_one_eq]
  intro hc
  simp only [Set.free_terms, Set.mem_iUnion] at hc
  obtain ⟨g, hg, hmem⟩ := hc
  obtain ⟨g0, _, rfl⟩ := hg
  have h1 : (2*m) ∈ (g0.rn zc).consts := const_mem_ft_iff.mp hmem
  have h2 := zc_consts_odd h1
  rw [Nat.mul_mod_right] at h2
  exact Nat.zero_ne_one h2

lemma no_even_in_z_consts (f : Formula σ) (m : ℕ) : (2*m) ∉ (znF 1 f).consts := by
  rw [znF_one_eq]
  intro hc
  have h2 := zc_consts_odd hc
  rw [Nat.mul_mod_right] at h2
  exact Nat.zero_ne_one h2

/- ### The truth lemma -/

private lemma tt_atomic (w : Set (Formula σ) × ℕ) (r : ℕ)
    (ts : Fin (σ.arity' r) → Term σ) (h : w ∈ (@M σ).W) :
    (Formula.force_form M w h (valL w.2) (Formula.atomic_formula r ts)
      ↔ (w.1 ⊢ Formula.atomic_formula r ts)) := by
  have harg : (Formula.atomic_formula r (fun i => (tmc w.2 (valL w.2 (ts i)) : Term σ)))
      = Formula.atomic_formula r ts := by
    congr 1
    funext i
    exact tmc_valL w.2 (ts i)
  constructor
  · rintro ⟨_, hmem⟩
    apply (closed h).mp
    rw [← harg]
    exact hmem
  · intro hp
    refine ⟨fun i => le_refl w.2, ?_⟩
    show Formula.atomic_formula r (fun i => (tmc w.2 (valL w.2 (ts i)) : Term σ)) ∈ w.1
    rw [harg]
    exact (closed h).mpr hp

private lemma tt_bot (w : Set (Formula σ) × ℕ) (h : w ∈ (@M σ).W) :
    (Formula.force_form M w h (valL w.2) (Formula.bottom) ↔ (w.1 ⊢ Formula.bottom)) := by
  constructor
  · intro hf
    exact hf.elim
  · intro hp
    exact absurd hp h.1

lemma model_tt_iff_prf_aux (n : ℕ) :
    ∀ (w : Set (Formula σ) × ℕ) (p : Formula σ), n ≥ p.size →
    ∀ (h : w ∈ (@M σ).W),
    (Formula.force_form M w h (valL w.2) p ↔ (w.1 ⊢ p)) := by
  induction n with
  | zero =>
    intro w p hc h
    cases p with
    | atomic_formula r ts => exact tt_atomic w r ts h
    | bottom => exact tt_bot w h
    | conjunction f1 f2 => simp at hc
    | disjunction f1 f2 => simp at hc
    | implication f1 f2 => simp at hc
    | existential_quantification f => simp at hc
    | universal_quantification f => simp at hc
  | succ n hn =>
    intro w p hc h
    cases p with
    | atomic_formula r ts => exact tt_atomic w r ts h
    | bottom => exact tt_bot w h
    | conjunction f1 f2 =>
      simp only [Formula.size, ge_iff_le] at hc
      have h01 : n ≥ f1.size := by linarith
      have h02 : n ≥ f2.size := by linarith
      constructor
      · rintro ⟨hf1, hf2⟩
        have h1 := (hn w f1 h01 h).mp hf1
        have h2 := (hn w f2 h02 h).mp hf2
        have h3 := Proof.introA h1 h2
        rw [Set.union_self] at h3
        exact h3
      · intro hp
        exact ⟨(hn w f1 h01 h).mpr (Proof.elimA1 hp),
               (hn w f2 h02 h).mpr (Proof.elimA2 hp)⟩
    | disjunction f1 f2 =>
      simp only [Formula.size, ge_iff_le] at hc
      have h01 : n ≥ f1.size := by linarith
      have h02 : n ≥ f2.size := by linarith
      constructor
      · rintro (hf1 | hf2)
        · exact Proof.introO1 _ ((hn w f1 h01 h).mp hf1)
        · exact Proof.introO2 _ ((hn w f2 h02 h).mp hf2)
      · intro hp
        cases h.2.2.1 f1 f2 ((closed h).mpr hp) with
        | inl h1 => exact Or.inl ((hn w f1 h01 h).mpr ((closed h).mp h1))
        | inr h2 => exact Or.inr ((hn w f2 h02 h).mpr ((closed h).mp h2))
    | implication f1 f2 =>
      simp only [Formula.size, ge_iff_le] at hc
      have h01 : n ≥ f1.size := by linarith
      have h02 : n ≥ f2.size := by linarith
      constructor
      · intro hf
        by_cases hc1 : ((w.1 ∪ {f1}) ⊢ f2)
        · exact Proof.introI hc1
        · exfalso
          have hnz : ¬ ((znF 1 '' (w.1 ∪ {f1})) ⊢ znF 1 f2) := by
            intro hz
            apply hc1
            apply (z_provable_iff _ _).mpr
            rw [znF_one_eq] at hz
            exact hz
          have hstd : std ((znF 1) '' (w.1 ∪ {f1})) (znF 1 f2) := by
            rw [znF_one_eq]
            exact z_image_std _ _
          have hnp := prime_no_prf hnz hstd
          have hworld : ((prime ((znF 1) '' (w.1 ∪ {f1})) (znF 1 f2), w.2+1) :
              Set (Formula σ) × ℕ) ∈ worlds :=
            ⟨consist_of_not_prf hnp, prime_of_prime⟩
          have hR : (@M σ).R w (prime ((znF 1) '' (w.1 ∪ {f1})) (znF 1 f2), w.2+1) := by
            refine ⟨⟨Nat.le_succ w.2, ?_⟩, hworld⟩
            show (znF ((w.2+1) - w.2)) '' w.1 ⊆ _
            rw [Nat.add_sub_cancel_left]
            intro g hg
            obtain ⟨g0, hg0, rfl⟩ := hg
            exact Or.inl ⟨g0, Or.inl hg0, rfl⟩
          have hf1force : Formula.force_form M
              (prime ((znF 1) '' (w.1 ∪ {f1})) (znF 1 f2), w.2+1) hworld (valL w.2) f1 := by
            rw [force_shift hworld (Nat.le_succ w.2)]
            show Formula.force_form M _ hworld (valL (w.2+1)) (znF ((w.2+1) - w.2) f1)
            rw [Nat.add_sub_cancel_left]
            apply (hn _ (znF 1 f1) (by rw [znF_size]; exact h01) hworld).mpr
            apply Proof.ref
            exact Or.inl ⟨f1, Or.inr rfl, rfl⟩
          have hf2force := hf _ hR hf1force
          have hf2shift := (force_shift hworld (Nat.le_succ w.2)).mp hf2force
          rw [Nat.add_sub_cancel_left] at hf2shift
          exact hnp ((hn _ (znF 1 f2) (by rw [znF_size]; exact h02) hworld).mp hf2shift)
      · intro hp
        intro u hru hfu1
        have hu : u ∈ worlds := hru.2
        have hkl : w.2 ≤ u.2 := hru.1.1
        have hzn : u.1 ⊢ znF (u.2 - w.2) (f1 →ᵢ f2) :=
          subset_proof (zn_provable hp) hru.1.2
        rw [znF_imp] at hzn
        have hf1p : u.1 ⊢ znF (u.2 - w.2) f1 :=
          (hn u (znF (u.2 - w.2) f1) (by rw [znF_size]; exact h01) hu).mp
            ((force_shift hu hkl).mp hfu1)
        have hf2p := Proof.elimI hzn hf1p
        exact (force_shift hu hkl).mpr
          ((hn u (znF (u.2 - w.2) f2) (by rw [znF_size]; exact h02) hu).mpr hf2p)
    | existential_quantification f =>
      simp only [Formula.size, ge_iff_le] at hc
      have h0 : n ≥ f.size := by linarith
      constructor
      · rintro ⟨t, htD, hforce⟩
        have hbridge := (bridge_univ h (le_refl w.2) t htD f).mp hforce
        rw [Nat.sub_self, znF_zero] at hbridge
        have hsz : n ≥ (f.inst (tmc w.2 t)).size := by
          have : (f.inst (tmc w.2 t)).size = f.size := by
            unfold Formula.inst
            simp
          rw [this]
          exact h0
        have hprf := (hn w (f.inst (tmc w.2 t)) hsz h).mp hbridge
        exact Proof.introE _ hprf
      · intro hp
        obtain ⟨m, c, hmem⟩ := h.2.2.2 f ((closed h).mpr hp)
        have hinst : w.1 ⊢ f.inst (Term.const c) :=
          (provable_p_bot _ _ m).mp (Proof.ref hmem)
        refine ⟨@valL σ w.2 (Term.const c), le_refl w.2, ?_⟩
        have hsz : n ≥ (f.inst (Term.const c)).size := by
          have : (f.inst (Term.const c)).size = f.size := by
            unfold Formula.inst
            simp
          rw [this]
          exact h0
        have hforce := (hn w (f.inst (Term.const c)) hsz h).mpr hinst
        rw [force_inst] at hforce
        exact hforce
    | universal_quantification f =>
      simp only [Formula.size, ge_iff_le] at hc
      have h0 : n ≥ f.size := by linarith
      constructor
      · intro hforce
        by_cases hp : (w.1 ⊢ (∀ᵢ f))
        · exact hp
        · exfalso
          have hz : ¬ ((znF 1 '' w.1) ⊢ (∀ᵢ (znF 1 f))) := by
            intro hzp
            apply hp
            apply (z_provable_iff _ _).mpr
            rw [znF_one_eq] at hzp
            exact hzp
          have hinp : ¬ ((znF 1 '' w.1) ⊢ ((znF 1 f).inst (Term.const 0))) := by
            intro hip
            apply hz
            apply const_gen hip
            · have h00 : (0:ℕ) = 2*0 := rfl
              rw [show (Term.const 0 : Term σ) = Term.const (2*0) from rfl]
              exact no_even_in_z_image w.1 0
            · rw [show (0:ℕ) = 2*0 from rfl]
              exact no_even_in_z_consts f 0
          have hstd : std ((znF 1) '' w.1) ((znF 1 f).inst (Term.const 0)) := by
            rw [znF_one_eq]
            exact z_image_std _ _
          have hnp := prime_no_prf hinp hstd
          have hworld : ((prime ((znF 1) '' w.1) ((znF 1 f).inst (Term.const 0)), w.2+1) :
              Set (Formula σ) × ℕ) ∈ worlds :=
            ⟨consist_of_not_prf hnp, prime_of_prime⟩
          have hR : (@M σ).R w
              (prime ((znF 1) '' w.1) ((znF 1 f).inst (Term.const 0)), w.2+1) := by
            refine ⟨⟨Nat.le_succ w.2, ?_⟩, hworld⟩
            show (znF ((w.2+1) - w.2)) '' w.1 ⊆ _
            rw [Nat.add_sub_cancel_left]
            intro g hg
            exact Or.inl hg
          have hforceI := hforce _ hR (@valL σ (w.2+1) (Term.const 0)) (le_refl (w.2+1))
          have hbridge := (bridge_univ hworld (Nat.le_succ w.2)
            (@valL σ (w.2+1) (Term.const 0)) (le_refl (w.2+1)) f).mp hforceI
          have htv : (tmc (w.2+1) (@valL σ (w.2+1) (Term.const 0)) : Term σ) = Term.const 0 :=
            tmc_valL (w.2+1) (Term.const 0)
          rw [Nat.add_sub_cancel_left, htv] at hbridge
          have hsz : n ≥ ((znF 1 f).inst (Term.const 0)).size := by
            have : ((znF 1 f).inst (Term.const 0)).size = f.size := by
              unfold Formula.inst
              simp
            rw [this]
            exact h0
          exact hnp ((hn _ ((znF 1 f).inst (Term.const 0)) hsz hworld).mp hbridge)
      · intro hp
        intro u hru t htD
        have hu : u ∈ worlds := hru.2
        have hkl : w.2 ≤ u.2 := hru.1.1
        have hzn : u.1 ⊢ znF (u.2 - w.2) (∀ᵢ f) :=
          subset_proof (zn_provable hp) hru.1.2
        rw [znF_all] at hzn
        have hinst := Proof.elimF (tmc u.2 t) hzn
        have hsz : n ≥ ((znF (u.2 - w.2) f).inst (tmc u.2 t)).size := by
          have : ((znF (u.2 - w.2) f).inst (tmc u.2 t)).size = f.size := by
            unfold Formula.inst
            simp
          rw [this]
          exact h0
        have hforce := (hn u ((znF (u.2 - w.2) f).inst (tmc u.2 t)) hsz hu).mpr hinst
        exact (bridge_univ hu hkl t htD f).mpr hforce

lemma model_tt_iff_prf {p : Formula σ} {w : Set (Formula σ) × ℕ}
    (h0 : w ∈ (@M σ).W) :
    (Formula.force_form M w h0 (valL w.2) p) ↔ (w.1 ⊢ p) :=
  model_tt_iff_prf_aux p.size w p (le_refl _) h0

/- ### Completeness under the standard condition -/

theorem completeness {Γ : Set (Formula σ)} {p : Formula σ} (hstd : std Γ p) :
    (Γ ⊧ p) → (Γ ⊢ p) := by
  by_contra hc
  push_neg at hc
  obtain ⟨hsem, hnp⟩ := hc
  have hd : ((prime Γ p, 0) : Set (Formula σ) × ℕ) ∈ worlds := by
    constructor
    · exact consist_of_not_prf (prime_no_prf hnp hstd)
    · exact prime_of_prime
  have hval : val_in (@M σ) (prime Γ p, 0) (valL 0) := by
    intro t
    show (0 : ℕ) ≤ 0
    exact le_refl 0
  have hforce := hsem M (prime Γ p, 0) (valL 0) hd hval ?_
  · have := (model_tt_iff_prf hd).mp hforce
    exact (prime_no_prf hnp hstd) this
  · intro f hf
    apply (model_tt_iff_prf hd).mpr
    apply Proof.ref
    left
    exact hf

end canonical
