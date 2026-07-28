/- Swapping two free variables preserves derivability.

`Term.swf a b d` / `Formula.swf a b d` exchange the free variables `a` and `b`,
where `d` counts the binders already crossed (so at depth `d` the outer variable
`x` is represented by the de Bruijn index `x + d`; bound indices `< d` are
untouched, as they can never equal `a+d` or `b+d`... they can only if the index
is ≥ d, which bound ones aren't).

The swap is an involution, so `swf_proof` transports derivations in both
directions; it is the tool that lets us re-target the fresh variable of a
derivation, which is the engine of the constant-generalization lemma
(`CLM/cv.lean`). -/

import CLM.IFOL
import CLM.general
open IFOL
open Set
open Classical

namespace IFOL

variable {σ : Signature}

/-- Swap on indices (at depth 0). -/
def sw (a b x : ℕ) : ℕ := if x = a then b else if x = b then a else x

def Term.swf (a b d : ℕ) : Term σ → Term σ
  | .free n => if n = a + d then .free (b + d) else if n = b + d then .free (a + d) else .free n
  | .const c => .const c

def Formula.swf (a b d : ℕ) : Formula σ → Formula σ
  | .atomic_formula r ts => .atomic_formula r (fun i => (ts i).swf a b d)
  | .conjunction f1 f2 => .conjunction (f1.swf a b d) (f2.swf a b d)
  | .disjunction f1 f2 => .disjunction (f1.swf a b d) (f2.swf a b d)
  | .implication f1 f2 => .implication (f1.swf a b d) (f2.swf a b d)
  | .existential_quantification f => .existential_quantification (f.swf a b (d+1))
  | .universal_quantification f => .universal_quantification (f.swf a b (d+1))
  | .bottom => .bottom

/- ### Computation helpers -/

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

/- ### Basic algebra -/

lemma sw_invol (a b x : ℕ) : sw a b (sw a b x) = x := by
  unfold sw
  split_ifs <;> simp_all

lemma swf_term_invol (a b d : ℕ) (t : Term σ) :
    Term.swf a b d (Term.swf a b d t) = t := by
  cases t with
  | const c => rfl
  | free n =>
    by_cases h1 : n = a + d
    · rw [swf_free_eq h1]
      by_cases h2 : b + d = a + d
      · rw [swf_free_eq h2, h1, ← h2]
      · rw [swf_free_eq' h2 rfl, h1]
    · by_cases h2 : n = b + d
      · rw [swf_free_eq' h1 h2, swf_free_eq rfl, h2]
      · rw [swf_free_ne h1 h2, swf_free_ne h1 h2]

lemma swf_invol (a b d : ℕ) (f : Formula σ) :
    Formula.swf a b d (Formula.swf a b d f) = f := by
  induction f generalizing d with
  | atomic_formula r ts => simp [Formula.swf, swf_term_invol]
  | conjunction f1 f2 ih1 ih2 => simp [Formula.swf, ih1, ih2]
  | disjunction f1 f2 ih1 ih2 => simp [Formula.swf, ih1, ih2]
  | implication f1 f2 ih1 ih2 => simp [Formula.swf, ih1, ih2]
  | existential_quantification f ih => simp [Formula.swf, ih]
  | universal_quantification f ih => simp [Formula.swf, ih]
  | bottom => rfl

lemma swf_term_inj (a b d : ℕ) : Function.Injective (Term.swf a b d : Term σ → Term σ) := by
  intro t1 t2 h
  have h2 := congrArg (Term.swf a b d) h
  rwa [swf_term_invol, swf_term_invol] at h2

@[simp]
lemma swf_size (a b d : ℕ) (f : Formula σ) : (f.swf a b d).size = f.size := by
  induction f generalizing d with
  | atomic_formula r ts => rfl
  | conjunction f1 f2 ih1 ih2 => simp [Formula.swf, ih1, ih2]
  | disjunction f1 f2 ih1 ih2 => simp [Formula.swf, ih1, ih2]
  | implication f1 f2 ih1 ih2 => simp [Formula.swf, ih1, ih2]
  | existential_quantification f ih => simp [Formula.swf, ih]
  | universal_quantification f ih => simp [Formula.swf, ih]
  | bottom => rfl

/-- Swapping a free variable at depth 0. -/
lemma swf_term_free (a b x : ℕ) :
    Term.swf a b 0 (Term.free x : Term σ) = Term.free (sw a b x) := by
  by_cases h1 : x = a
  · rw [swf_free_eq (show x = a + 0 from h1), show sw a b x = b from by unfold sw; rw [if_pos h1]]
    rfl
  · by_cases h2 : x = b
    · rw [swf_free_eq' (show ¬ x = a + 0 from h1) (show x = b + 0 from h2),
        show sw a b x = a from by unfold sw; rw [if_neg h1, if_pos h2]]
      rfl
    · rw [swf_free_ne (show ¬ x = a + 0 from h1) (show ¬ x = b + 0 from h2),
        show sw a b x = x from by unfold sw; rw [if_neg h1, if_neg h2]]

/- ### Commutation with lift -/

lemma swf_term_lift {a b k d : ℕ} (hk : k ≤ d) (t : Term σ) :
    Term.swf a b (d+1) (Term.lift k t) = Term.lift k (Term.swf a b d t) := by
  cases t with
  | const c => rfl
  | free n =>
    by_cases h1 : n < k
    · have ha1 : ¬ n = a + (d+1) := by intro h; linarith
      have hb1 : ¬ n = b + (d+1) := by intro h; linarith
      have ha0 : ¬ n = a + d := by intro h; linarith
      have hb0 : ¬ n = b + d := by intro h; linarith
      rw [lift_free_lt h1, swf_free_ne ha1 hb1, swf_free_ne ha0 hb0, lift_free_lt h1]
    · by_cases h2 : n = a + d
      · have e1 : n + 1 = a + (d+1) := by rw [h2]; rfl
        have hbk : ¬ b + d < k := by intro h; linarith
        rw [lift_free_ge h1, swf_free_eq e1, swf_free_eq h2, lift_free_ge hbk]
        rfl
      · by_cases h3 : n = b + d
        · have e1 : ¬ n + 1 = a + (d+1) := by intro h; apply h2; linarith
          have e2 : n + 1 = b + (d+1) := by rw [h3]; rfl
          have hak : ¬ a + d < k := by intro h; linarith
          rw [lift_free_ge h1, swf_free_eq' e1 e2, swf_free_eq' h2 h3, lift_free_ge hak]
          rfl
        · have e1 : ¬ n + 1 = a + (d+1) := by intro h; apply h2; linarith
          have e2 : ¬ n + 1 = b + (d+1) := by intro h; apply h3; linarith
          rw [lift_free_ge h1, swf_free_ne e1 e2, swf_free_ne h2 h3, lift_free_ge h1]

lemma swf_lift {a b k d : ℕ} (hk : k ≤ d) (f : Formula σ) :
    Formula.swf a b (d+1) (f.lift k) = (Formula.swf a b d f).lift k := by
  induction f generalizing k d with
  | atomic_formula r ts =>
    simp only [Formula.lift, Formula.swf]
    congr 1
    funext i
    exact swf_term_lift hk _
  | conjunction f1 f2 ih1 ih2 =>
    simp only [Formula.lift, Formula.swf]; rw [ih1 hk, ih2 hk]
  | disjunction f1 f2 ih1 ih2 =>
    simp only [Formula.lift, Formula.swf]; rw [ih1 hk, ih2 hk]
  | implication f1 f2 ih1 ih2 =>
    simp only [Formula.lift, Formula.swf]; rw [ih1 hk, ih2 hk]
  | existential_quantification f ih =>
    simp only [Formula.lift, Formula.swf]; rw [ih (Nat.succ_le_succ hk)]
  | universal_quantification f ih =>
    simp only [Formula.lift, Formula.swf]; rw [ih (Nat.succ_le_succ hk)]
  | bottom => rfl

/- ### Commutation with instantiation -/

private lemma swf_subst_down_term {a b : ℕ} (j d : ℕ) (hjd : j ≤ d) (t e : Term σ)
    (he : ∀ m, e = Term.free m → j < m) :
    Term.swf a b d (Term.down j (Term.Substitution t (Term.free j) e))
      = Term.down j (Term.Substitution (Term.swf a b (d+1) t) (Term.free j) (Term.swf a b (d+1) e)) := by
  cases t with
  | const c => rfl
  | free n =>
    by_cases h1 : n = j
    · rw [subst_free_eq e h1]
      have haj : ¬ n = a + (d+1) := by intro h; linarith
      have hbj : ¬ n = b + (d+1) := by intro h; linarith
      rw [swf_free_ne haj hbj, subst_free_eq _ h1]
      cases e with
      | const c => rfl
      | free m =>
        have hm : j < m := he m rfl
        have hmj : ¬ m < j := by intro h; linarith
        rw [down_free_ge hmj]
        by_cases h2 : m = a + (d+1)
        · have e1 : m - 1 = a + d := by rw [h2]; rfl
          have hf : ¬ b + (d+1) < j := by intro h; linarith
          rw [swf_free_eq e1, swf_free_eq h2, down_free_ge hf]
          rfl
        · by_cases h3 : m = b + (d+1)
          · have hm1 : m - 1 + 1 = m := Nat.succ_pred_eq_of_pos (lt_of_le_of_lt (Nat.zero_le j) hm)
            have e1 : ¬ m - 1 = a + d := by intro h; apply h2; rw [← hm1, h]; rfl
            have e2 : m - 1 = b + d := by rw [h3]; rfl
            have hf : ¬ a + (d+1) < j := by intro h; linarith
            rw [swf_free_eq' e1 e2, swf_free_eq' h2 h3, down_free_ge hf]
            rfl
          · have hm1 : m - 1 + 1 = m := Nat.succ_pred_eq_of_pos (lt_of_le_of_lt (Nat.zero_le j) hm)
            have e1 : ¬ m - 1 = a + d := by intro h; apply h2; rw [← hm1, h]; rfl
            have e2 : ¬ m - 1 = b + d := by intro h; apply h3; rw [← hm1, h]; rfl
            rw [swf_free_ne e1 e2, swf_free_ne h2 h3, down_free_ge hmj]
    · rw [subst_free_ne e h1]
      by_cases h2 : n < j
      · have ha0 : ¬ n = a + d := by intro h; linarith
        have hb0 : ¬ n = b + d := by intro h; linarith
        have ha1 : ¬ n = a + (d+1) := by intro h; linarith
        have hb1 : ¬ n = b + (d+1) := by intro h; linarith
        rw [down_free_lt h2, swf_free_ne ha0 hb0, swf_free_ne ha1 hb1,
          subst_free_ne _ h1, down_free_lt h2]
      · have hn : j < n := Nat.lt_of_le_of_ne (Nat.le_of_not_lt h2) (Ne.symm h1)
        have hn1 : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos (lt_of_le_of_lt (Nat.zero_le j) hn)
        rw [down_free_ge h2]
        by_cases h3 : n = a + (d+1)
        · have e1 : n - 1 = a + d := by rw [h3]; rfl
          have hj : ¬ b + (d+1) = j := by intro h; linarith
          have hf : ¬ b + (d+1) < j := by intro h; linarith
          rw [swf_free_eq e1, swf_free_eq h3, subst_free_ne _ hj, down_free_ge hf]
          rfl
        · by_cases h4 : n = b + (d+1)
          · have e1 : ¬ n - 1 = a + d := by intro h; apply h3; rw [← hn1, h]; rfl
            have e2 : n - 1 = b + d := by rw [h4]; rfl
            have hj : ¬ a + (d+1) = j := by intro h; linarith
            have hf : ¬ a + (d+1) < j := by intro h; linarith
            rw [swf_free_eq' e1 e2, swf_free_eq' h3 h4, subst_free_ne _ hj, down_free_ge hf]
            rfl
          · have e1 : ¬ n - 1 = a + d := by intro h; apply h3; rw [← hn1, h]; rfl
            have e2 : ¬ n - 1 = b + d := by intro h; apply h4; rw [← hn1, h]; rfl
            rw [swf_free_ne e1 e2, swf_free_ne h3 h4, subst_free_ne _ h1, down_free_ge h2]

/-- Core lemma: swapping past a `Substitution (free j) e` followed by `down j`,
where `e` mentions no free index `≤ j` (in the application `e` is an iterated
lift of the instantiating term, so this holds). -/
lemma swf_inst_aux {a b : ℕ} :
    ∀ (A : Formula σ) (j d : ℕ) (e : Term σ), j ≤ d →
    (∀ m, e = Term.free m → j < m) →
    Formula.swf a b d ((A.Substitution (Term.free j) e).down j)
      = ((Formula.swf a b (d+1) A).Substitution (Term.free j) (Term.swf a b (d+1) e)).down j := by
  intro A
  induction A with
  | atomic_formula r ts =>
    intro j d e hjd he
    simp only [Formula.Substitution, Formula.down, Formula.swf]
    congr 1
    funext i
    exact swf_subst_down_term j d hjd (ts i) e he
  | conjunction f1 f2 ih1 ih2 =>
    intro j d e hjd he
    simp only [Formula.Substitution, Formula.down, Formula.swf]
    rw [ih1 j d e hjd he, ih2 j d e hjd he]
  | disjunction f1 f2 ih1 ih2 =>
    intro j d e hjd he
    simp only [Formula.Substitution, Formula.down, Formula.swf]
    rw [ih1 j d e hjd he, ih2 j d e hjd he]
  | implication f1 f2 ih1 ih2 =>
    intro j d e hjd he
    simp only [Formula.Substitution, Formula.down, Formula.swf]
    rw [ih1 j d e hjd he, ih2 j d e hjd he]
  | existential_quantification f ih =>
    intro j d e hjd he
    simp only [Formula.Substitution, Formula.down, Formula.swf]
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
      swf_term_lift (Nat.zero_le (d+1)) e]
  | universal_quantification f ih =>
    intro j d e hjd he
    simp only [Formula.Substitution, Formula.down, Formula.swf]
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
      swf_term_lift (Nat.zero_le (d+1)) e]
  | bottom => intro j d e hjd he; rfl

lemma swf_inst (a b d : ℕ) (A : Formula σ) (τ : Term σ) :
    Formula.swf a b d (A.inst τ)
      = (Formula.swf a b (d+1) A).inst (Term.swf a b d τ) := by
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
  rw [swf_inst_aux A 0 d (τ.lift 0) (Nat.zero_le d) he,
    swf_term_lift (Nat.zero_le d) τ]

/- ### Commutation with generalization -/

private lemma swf_gen_term {a b x : ℕ} (t : Term σ) (j : ℕ) :
    Term.swf a b (j+1) (Term.Substitution t (Term.free (x+j+1)) (Term.free j))
      = Term.Substitution (Term.swf a b (j+1) t) (Term.free ((sw a b x)+j+1)) (Term.free j) := by
  cases t with
  | const c => rfl
  | free n =>
    by_cases h1 : n = x+j+1
    · rw [subst_free_eq _ h1]
      have hja : ¬ j = a + (j+1) := by intro h; linarith
      have hjb : ¬ j = b + (j+1) := by intro h; linarith
      rw [swf_free_ne hja hjb]
      by_cases h2 : x = a
      · have hn : n = a + (j+1) := by rw [h1, h2]; rfl
        have hs : sw a b x = b := by unfold sw; rw [if_pos h2]
        rw [swf_free_eq hn, hs, subst_free_eq (Term.free j) (show b+(j+1) = b+j+1 from rfl)]
      · have hna : ¬ n = a + (j+1) := by intro h; apply h2; linarith
        by_cases h3 : x = b
        · have hnb : n = b + (j+1) := by rw [h1, h3]; rfl
          have hs : sw a b x = a := by unfold sw; rw [if_neg h2, if_pos h3]
          rw [swf_free_eq' hna hnb, hs,
            subst_free_eq (Term.free j) (show a+(j+1) = a+j+1 from rfl)]
        · have hnb : ¬ n = b + (j+1) := by intro h; apply h3; linarith
          have hs : sw a b x = x := by unfold sw; rw [if_neg h2, if_neg h3]
          rw [swf_free_ne hna hnb, hs, subst_free_eq (Term.free j) h1]
    · rw [subst_free_ne _ h1]
      by_cases h2 : n = a + (j+1)
      · have hxa : ¬ x = a := by intro h; apply h1; rw [h2, h]; rfl
        have hsb : ¬ sw a b x = b := by
          unfold sw; split_ifs with c1 c2
          · intro hab; apply h1; rw [h2, c1, hab]; rfl
          · exact c1
        have hne : ¬ b + (j+1) = sw a b x + j + 1 := by intro h; apply hsb; linarith
        rw [swf_free_eq h2, subst_free_ne _ hne]
      · by_cases h3 : n = b + (j+1)
        · have hxb : ¬ x = b := by intro h; apply h1; rw [h3, h]; rfl
          have hsa : ¬ sw a b x = a := by
            unfold sw; split_ifs with c1 c2
            · intro hba; apply h2; rw [h3, hba]
            · exact c1
          have hne : ¬ a + (j+1) = sw a b x + j + 1 := by intro h; apply hsa; linarith
          rw [swf_free_eq' h2 h3, subst_free_ne _ hne]
        · have hne : ¬ n = sw a b x + j + 1 := by
            unfold sw; split_ifs with c1 c2
            · intro h; apply h3; rw [h]; rfl
            · intro h; apply h2; rw [h]; rfl
            · intro h; apply h1; rw [h]
          rw [swf_free_ne h2 h3, subst_free_ne _ hne]

lemma swf_gen_aux {a b x : ℕ} :
    ∀ (A : Formula σ) (j : ℕ),
    Formula.swf a b (j+1) (A.Substitution (Term.free (x+j+1)) (Term.free j))
      = (Formula.swf a b (j+1) A).Substitution (Term.free ((sw a b x)+j+1)) (Term.free j) := by
  intro A
  induction A with
  | atomic_formula r ts =>
    intro j
    simp only [Formula.Substitution, Formula.swf]
    congr 1
    funext i
    exact swf_gen_term (ts i) j
  | conjunction f1 f2 ih1 ih2 =>
    intro j
    simp only [Formula.Substitution, Formula.swf]
    rw [ih1 j, ih2 j]
  | disjunction f1 f2 ih1 ih2 =>
    intro j
    simp only [Formula.Substitution, Formula.swf]
    rw [ih1 j, ih2 j]
  | implication f1 f2 ih1 ih2 =>
    intro j
    simp only [Formula.Substitution, Formula.swf]
    rw [ih1 j, ih2 j]
  | existential_quantification f ih =>
    intro j
    simp only [Formula.Substitution, Formula.swf]
    have hA : ((Term.free (x+j+1)).lift 0 : Term σ) = Term.free (x+(j+1)+1) :=
      lift_free_ge (Nat.not_lt_zero _)
    have hS : ((Term.free ((sw a b x)+j+1)).lift 0 : Term σ) = Term.free ((sw a b x)+(j+1)+1) :=
      lift_free_ge (Nat.not_lt_zero _)
    have hj : ((Term.free j).lift 0 : Term σ) = Term.free (j+1) :=
      lift_free_ge (Nat.not_lt_zero _)
    rw [hA, hS, hj, ih (j+1)]
  | universal_quantification f ih =>
    intro j
    simp only [Formula.Substitution, Formula.swf]
    have hA : ((Term.free (x+j+1)).lift 0 : Term σ) = Term.free (x+(j+1)+1) :=
      lift_free_ge (Nat.not_lt_zero _)
    have hS : ((Term.free ((sw a b x)+j+1)).lift 0 : Term σ) = Term.free ((sw a b x)+(j+1)+1) :=
      lift_free_ge (Nat.not_lt_zero _)
    have hj : ((Term.free j).lift 0 : Term σ) = Term.free (j+1) :=
      lift_free_ge (Nat.not_lt_zero _)
    rw [hA, hS, hj, ih (j+1)]
  | bottom => intro j; rfl

lemma swf_gen (a b x : ℕ) (A : Formula σ) :
    Formula.swf a b 1 (A.gen x) = (Formula.swf a b 0 A).gen (sw a b x) := by
  unfold Formula.gen
  have h := swf_gen_aux (a := a) (b := b) (x := x) (A.lift 0) 0
  rw [swf_lift (le_refl 0)] at h
  exact h

/- ### Free terms -/

private lemma ft_free_ge {z d : ℕ} (h : z ≥ d) :
    Term.free_terms (Term.free z : Term σ) d = {Term.free (z-d)} := by
  show (if z ≥ d then ({Term.free (z-d)} : Set (Term σ)) else ∅) = {Term.free (z-d)}
  rw [if_pos h]

private lemma ft_free_lt {z d : ℕ} (h : ¬ z ≥ d) :
    Term.free_terms (Term.free z : Term σ) d = ∅ := by
  show (if z ≥ d then ({Term.free (z-d)} : Set (Term σ)) else ∅) = ∅
  rw [if_neg h]

private lemma swf_term_free_terms (a b : ℕ) (t : Term σ) (d : ℕ) :
    (Term.swf a b d t).free_terms d = (Term.swf a b 0) '' (t.free_terms d) := by
  cases t with
  | const c =>
    show (Term.const c : Term σ).free_terms d = _
    rw [show (Term.const c : Term σ).free_terms d = {Term.const c} from rfl,
      Set.image_singleton]
    rfl
  | free z =>
    by_cases h1 : z ≥ d
    · by_cases h2 : z = a + d
      · have hz : z - d = a := by rw [h2]; exact Nat.add_sub_cancel a d
        have eL : (Term.free (b+d) : Term σ).free_terms d = {Term.free b} := by
          rw [ft_free_ge (Nat.le_add_left d b), Nat.add_sub_cancel]
        have eR : (Term.free z : Term σ).free_terms d = {Term.free a} := by
          rw [ft_free_ge h1, hz]
        rw [swf_free_eq h2, eL, eR, Set.image_singleton,
          swf_free_eq (show a = a + 0 from rfl)]
        rfl
      · by_cases h3 : z = b + d
        · have hz : z - d = b := by rw [h3]; exact Nat.add_sub_cancel b d
          have eL : (Term.free (a+d) : Term σ).free_terms d = {Term.free a} := by
            rw [ft_free_ge (Nat.le_add_left d a), Nat.add_sub_cancel]
          have eR : (Term.free z : Term σ).free_terms d = {Term.free b} := by
            rw [ft_free_ge h1, hz]
          have hba : ¬ b = a + 0 := by
            intro h
            rw [Nat.add_zero] at h
            apply h2
            rw [h3, h]
          rw [swf_free_eq' h2 h3, eL, eR, Set.image_singleton,
            swf_free_eq' hba (show b = b + 0 from rfl)]
          rfl
        · have eR : (Term.free z : Term σ).free_terms d = {Term.free (z-d)} := by
            rw [ft_free_ge h1]
          have ha : ¬ z - d = a + 0 := by
            intro h
            rw [Nat.add_zero] at h
            exact h2 ((Nat.sub_eq_iff_eq_add h1).mp h)
          have hb : ¬ z - d = b + 0 := by
            intro h
            rw [Nat.add_zero] at h
            exact h3 ((Nat.sub_eq_iff_eq_add h1).mp h)
          rw [swf_free_ne h2 h3, eR, Set.image_singleton, swf_free_ne ha hb]
    · have ha : ¬ z = a + d := by intro h; apply h1; rw [h]; exact Nat.le_add_left d a
      have hb : ¬ z = b + d := by intro h; apply h1; rw [h]; exact Nat.le_add_left d b
      have e0 : (Term.free z : Term σ).free_terms d = ∅ := ft_free_lt h1
      rw [swf_free_ne ha hb, e0, Set.image_empty]

lemma swf_free_terms (a b : ℕ) :
    ∀ (f : Formula σ) (d : ℕ),
    (Formula.swf a b d f).free_terms d = (Term.swf a b 0) '' (f.free_terms d) := by
  intro f
  induction f with
  | atomic_formula r ts =>
    intro d
    simp only [Formula.swf, Formula.free_terms]
    rw [Set.image_iUnion]
    exact Set.iUnion_congr (fun i => swf_term_free_terms a b (ts i) d)
  | conjunction f1 f2 ih1 ih2 =>
    intro d
    simp only [Formula.swf, Formula.free_terms]
    rw [Set.image_union, ih1 d, ih2 d]
  | disjunction f1 f2 ih1 ih2 =>
    intro d
    simp only [Formula.swf, Formula.free_terms]
    rw [Set.image_union, ih1 d, ih2 d]
  | implication f1 f2 ih1 ih2 =>
    intro d
    simp only [Formula.swf, Formula.free_terms]
    rw [Set.image_union, ih1 d, ih2 d]
  | existential_quantification f ih =>
    intro d
    simp only [Formula.swf, Formula.free_terms]
    exact ih (d+1)
  | universal_quantification f ih =>
    intro d
    simp only [Formula.swf, Formula.free_terms]
    exact ih (d+1)
  | bottom =>
    intro d
    simp only [Formula.swf, Formula.free_terms]
    rw [Set.image_empty]

lemma swf_set_free_terms (a b : ℕ) (Γ : Set (Formula σ)) :
    Set.free_terms ((Formula.swf a b 0) '' Γ) = (Term.swf a b 0) '' (Set.free_terms Γ) := by
  unfold Set.free_terms
  rw [Set.biUnion_image, Set.image_iUnion₂]
  simp only [swf_free_terms]

lemma swf_not_mem_ft {a b : ℕ} {τ : Term σ} {f : Formula σ}
    (h : τ ∉ f.free_terms 0) :
    Term.swf a b 0 τ ∉ (Formula.swf a b 0 f).free_terms 0 := by
  rw [swf_free_terms]
  rintro ⟨s, hs, heq⟩
  have hst := swf_term_inj a b 0 heq
  rw [hst] at hs
  exact h hs

lemma swf_not_mem_set_ft {a b : ℕ} {τ : Term σ} {Γ : Set (Formula σ)}
    (h : τ ∉ Set.free_terms Γ) :
    Term.swf a b 0 τ ∉ Set.free_terms ((Formula.swf a b 0) '' Γ) := by
  rw [swf_set_free_terms]
  rintro ⟨s, hs, heq⟩
  have hst := swf_term_inj a b 0 heq
  rw [hst] at hs
  exact h hs

lemma swf_free_var_mem {a b x : ℕ} {Γ : Set (Formula σ)} :
    (Term.free (sw a b x)) ∈ Set.free_terms ((Formula.swf a b 0) '' Γ) ↔
      (Term.free x) ∈ Set.free_terms Γ := by
  rw [swf_set_free_terms]
  constructor
  · rintro ⟨s, hs, heq⟩
    cases s with
    | const c => simp [Term.swf] at heq
    | free y =>
      rw [swf_term_free] at heq
      injection heq with hy
      have h2 := congrArg (sw a b) hy
      rw [sw_invol, sw_invol] at h2
      rwa [h2] at hs
  · intro hx
    exact ⟨Term.free x, hx, swf_term_free a b x⟩

private lemma swf_term_id_of_not_mem {a b : ℕ} (t : Term σ) (d : ℕ)
    (ha : (Term.free a : Term σ) ∉ t.free_terms d)
    (hb : (Term.free b : Term σ) ∉ t.free_terms d) :
    Term.swf a b d t = t := by
  cases t with
  | const c => rfl
  | free n =>
    have hna : ¬ n = a + d := by
      intro h
      apply ha
      rw [ft_free_ge (show n ≥ d from by rw [h]; exact Nat.le_add_left d a), h, Nat.add_sub_cancel]
      rfl
    have hnb : ¬ n = b + d := by
      intro h
      apply hb
      rw [ft_free_ge (show n ≥ d from by rw [h]; exact Nat.le_add_left d b), h, Nat.add_sub_cancel]
      rfl
    exact swf_free_ne hna hnb

private lemma swf_id_aux {a b : ℕ} :
    ∀ (f : Formula σ) (d : ℕ), (Term.free a : Term σ) ∉ f.free_terms d →
      (Term.free b : Term σ) ∉ f.free_terms d → Formula.swf a b d f = f := by
  intro f
  induction f with
  | atomic_formula r ts =>
    intro d ha hb
    simp only [Formula.swf]
    congr 1
    funext i
    apply swf_term_id_of_not_mem
    · exact fun hc => ha (Set.mem_iUnion.mpr ⟨i, hc⟩)
    · exact fun hc => hb (Set.mem_iUnion.mpr ⟨i, hc⟩)
  | conjunction f1 f2 ih1 ih2 =>
    intro d ha hb
    simp only [Formula.swf]
    rw [ih1 d (fun hc => ha (Set.mem_union_left _ hc)) (fun hc => hb (Set.mem_union_left _ hc)),
      ih2 d (fun hc => ha (Set.mem_union_right _ hc)) (fun hc => hb (Set.mem_union_right _ hc))]
  | disjunction f1 f2 ih1 ih2 =>
    intro d ha hb
    simp only [Formula.swf]
    rw [ih1 d (fun hc => ha (Set.mem_union_left _ hc)) (fun hc => hb (Set.mem_union_left _ hc)),
      ih2 d (fun hc => ha (Set.mem_union_right _ hc)) (fun hc => hb (Set.mem_union_right _ hc))]
  | implication f1 f2 ih1 ih2 =>
    intro d ha hb
    simp only [Formula.swf]
    rw [ih1 d (fun hc => ha (Set.mem_union_left _ hc)) (fun hc => hb (Set.mem_union_left _ hc)),
      ih2 d (fun hc => ha (Set.mem_union_right _ hc)) (fun hc => hb (Set.mem_union_right _ hc))]
  | existential_quantification f ih =>
    intro d ha hb
    simp only [Formula.swf]
    rw [ih (d+1) ha hb]
  | universal_quantification f ih =>
    intro d ha hb
    simp only [Formula.swf]
    rw [ih (d+1) ha hb]
  | bottom => intro d ha hb; rfl

/-- If neither swapped variable occurs, the swap is the identity. -/
lemma swf_id_of_not_mem {a b : ℕ} {f : Formula σ}
    (ha : Term.free a ∉ f.free_terms 0) (hb : Term.free b ∉ f.free_terms 0) :
    Formula.swf a b 0 f = f :=
  swf_id_aux f 0 ha hb

/- ### The main theorem -/

theorem swf_proof {a b : ℕ} {Γ : Set (Formula σ)} {B : Formula σ} (h : Γ ⊢ B) :
    ((Formula.swf a b 0) '' Γ) ⊢ (Formula.swf a b 0 B) := by
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
  | introF h hx ih =>
    simp only [Formula.swf]
    rw [swf_gen]
    exact Proof.introF ih (fun hc => hx (swf_free_var_mem.mp hc))
  | elimF τ h ih =>
    rw [swf_inst]
    exact Proof.elimF (Term.swf a b 0 τ) ih
  | introE τ h ih =>
    simp only [Formula.swf]
    apply Proof.introE (Term.swf a b 0 τ)
    rw [← swf_inst]
    exact ih
  | elimE h1 h2 hτΔ hτB hτA ih1 ih2 =>
    rw [Set.image_union]
    rw [Set.image_union, Set.image_singleton, swf_inst a b 0] at ih2
    simp only [Formula.swf] at ih1
    exact Proof.elimE ih1 ih2 (swf_not_mem_set_ft hτΔ) (swf_not_mem_ft hτB)
      (swf_not_mem_ft hτA)

end IFOL
