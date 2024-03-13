import CLM.completeness
open IFOL

def is_consist(Γ :  Set (Formula σ)) := ∀ p ∈ Γ, (¬ (Γ ⊢ p)) ∨ (¬ (Γ ⊢ ¬ᵢ p))

def worlds: Set (Set (Formula σ)) := {w: Set (Formula σ)| is_consist w ∧is_prime w}





lemma consist_of_not_prf {Γ :  Set (Formula σ)} {p : Formula σ} :
  ¬ (Γ ⊢ p) → is_consist Γ :=
  by intro h q hq;right;intro h1;apply h;
     have z:= Proof.ref hq
     apply Proof.ine _ _ _ z h1

namespace canonical

def M {σ : Signature} : model (σ) where
  world := Set (Formula σ)
  W := worlds
  A := ℕ
  R := λ w v=> (w ⊆ v) ∧ v ∈ worlds
  D := λ _ => ∅
  β := λ _ => ∅
  α := fun w r map =>(@Formula.atomic_formula σ r (fun x=> Term.const (Constant.Constant (map x))))∈ w
  refl := λ w v => by simp;constructor;rfl;exact v
  obj_inc := λ w v v' h => by simp
  R_closed := λ w v v' h => by simp at v';exact v'.2
  trans := λ w v v' v'' h1 h2 => by simp; intro h3 h4 h5 h6;constructor;exact Set.Subset.trans h3 h5;exact h6


  mono := by
    intro u v hu hv r ts huv hn
    have h1:= huv.left hn
    exact h1

def val0 {σ: Signature} (t: Term σ) : ℕ := 0



lemma model_tt_iff_prf {p : Formula σ}(h0:w ∈ M.W ) :
  (Formula.force_form M w h0 val0 p) → (w ⊢ p) := by
  intro hw
  induction p with
  | atomic_formula r ts=>
    apply Proof.ref
    have z: w ∈ worlds := h0
    unfold worlds at z
    have z2:=z.right
    have z3:=z2.left
    unfold Formula.force_form at hw
    unfold model.α at hw
    simp at hw
    sorry






  | conjunction f1 f2 h1 h2 =>
  | disjunction f1 f2 h1 h2 =>
  | implication f1 f2 h1 h2 =>
  | negation f h =>
  | bottom =>
  | existential_quantification f h =>
  | universal_quantification f h =>


theorem completeness {Γ :  Set (Formula σ)} {p : Formula σ} :
  (Γ ⊧ p) → (Γ ⊢ p) :=by
  by_contra h;push_neg at h;
  have hd: (prime Γ p ) ∈ worlds := by
    constructor
    apply consist_of_not_prf
    exact prime_no_prf h.right
    exact prime_of_prime
  apply absurd
  fapply h.left
  exact M
  exact prime Γ p
  exact val0
  exact hd

  intro hpm
  apply prime_no_prf h.right
  apply (model_tt_iff_prf hd)
  exact hpm
 