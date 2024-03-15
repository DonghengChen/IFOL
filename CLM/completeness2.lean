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

@[simp]
def M {σ : Signature} : model (σ) where
  world := Set (Formula σ)
  W := worlds
  A := ℕ
  R := λ w v=> (w ⊆ v) ∧ v ∈ worlds
  D := λ _ => ∅
  β := λ _ => ∅
  α := fun w r map =>
    @Formula.atomic_formula σ r (fun x=>match (@Encodable.decode (Term σ) _ (map x) ) with
                                        | some t => t
                                        | none => Term.const (Constant.Constant 0))∈ w
  refl := λ w v => by simp;constructor;rfl;exact v
  obj_inc := λ w v v' h => by simp
  R_closed := λ w v v' h => by simp at v';exact v'.2
  trans := λ w v v' v'' h1 h2 => by simp; intro h3 h4 h5 h6;constructor;exact Set.Subset.trans h3 h5;exact h6
  mono := by
    intro u v hu hv r ts huv hn
    have h1:= huv.left hn
    exact h1

def val0 {σ: Signature} (t: Term σ) : ℕ := @Encodable.encode (Term σ) _ t

lemma closed{p : Formula σ}{w: Set (Formula σ)}(h0:w ∈ M.W ) :
  (p ∈ w) ↔ (w ⊢ p) := by
    constructor
    intro h;apply Proof.ref h
    intro h
    simp at h0
    unfold worlds at h0
    have h1:=h0.right.left
    apply h1
    exact h


lemma model_tt_iff_mem_p {w: Set (Formula σ)}(h0:w ∈ M.W )(n:Nat):
  ∀(p : Formula σ),(n≥p.size) → ((Formula.force_form M w h0 val0 p) ↔ (p ∈ w)) := by
  intro p hc
  induction n generalizing p
  case zero => simp at hc
               unfold Formula.size at hc
               cases p with
               | atomic_formula r ts=>  constructor
                                        intro hw
                                        unfold Formula.force_form at hw
                                        simp at hw
                                        unfold val0 at hw
                                        simp [Encodable.encodek] at hw
                                        exact hw
                                        intro hp
                                        unfold Formula.force_form
                                        simp
                                        unfold val0
                                        simp [Encodable.encodek]
                                        exact hp
                | conjunction f1 f2  => simp at hc
                | disjunction f1 f2  => simp at hc
                | implication f1 f2  => simp at hc
                | negation f  => simp at hc
                | existential_quantification f  => simp at hc
                | universal_quantification f  => simp at hc
  case succ n hn =>
        cases p with
        | atomic_formula r ts=>
          constructor
          intro hw
          unfold Formula.force_form at hw
          simp at hw
          unfold val0 at hw
          simp [Encodable.encodek] at hw
          exact hw
          intro hp
          unfold Formula.force_form
          simp
          unfold val0
          simp [Encodable.encodek]
          exact hp

        | conjunction f1 f2 =>
          simp at hc
          have h01:n ≥ f1.size:= by linarith
          have h02:n ≥ f2.size:= by linarith
          have h1:=hn f1 h01
          have h2:=hn f2 h02
          constructor
          intro h
          unfold Formula.force_form at h
          have h1:=Proof.ref (h1.mp h.left)
          have h2:=Proof.ref (h2.mp h.right)
          apply (closed h0).mpr
          have h3:= Proof.introA _ _ _ _ h1 h2
          rw [Set.union_self] at h3
          exact h3
          intro h
          have h:=(closed h0).mp h
          have h3:=Proof.elimA1 _ _ _ h
          have h3:=(closed h0).mpr h3
          have h4:=Proof.elimA2 _ _ _ h
          have h4:=(closed h0).mpr h4
          have h3:=h1.mpr h3
          have h4:=h2.mpr h4
          constructor
          exact h3
          exact h4

        | disjunction f1 f2=>
          simp at hc
          have h01:n ≥ f1.size:= by linarith
          have h02:n ≥ f2.size:= by linarith
          have h1:=hn f1 h01
          have h2:=hn f2 h02
          constructor
          intro h
          simp at h0
          apply (closed h0).mpr
          unfold Formula.force_form at h
          cases h with
          | inl ht=>have h1:=Proof.ref (h1.mp ht);exact (Proof.introO1  _ _ _ h1)
          | inr ht=>have h2:=Proof.ref (h2.mp ht);exact (Proof.introO2  _ _ _ h2)
          intro h
          simp at h0
          have h0:=h0.right.right.left f1 f2 h
          unfold Formula.force_form
          cases h0 with
          | inl ht=>have h1:=h1.mpr ht;left;exact h1
          | inr ht=>have h2:=h2.mpr ht;right;exact h2

        | implication f1 f2 =>
            simp at hc
            have h01:n ≥ f1.size:= by linarith
            have h02:n ≥ f2.size:= by linarith
            have h1:=hn f1 h01
            have h2:=hn f2 h02
            constructor
            intro h
            unfold Formula.force_form at h
            apply (closed h0).mpr
            apply Proof.introI f1 f2 w
            have hr: model.R M w w := by simp;constructor;rfl;simp at h0;exact h0
            have hz:=h w hr
            rw [h1,h2] at hz
            rw [closed h0] at hz
            rw [closed h0] at hz
            by_cases hwf1: is_consist (w ∪ {f1})
            sorry

            unfold is_consist at hwf1
            push_neg at hwf1
            cases hwf1;rename_i p hp
            apply Proof.ine _ _ _ hp.right.left hp.right.right
            intro h
            unfold Formula.force_form
            have h:=(closed h0).mp h
            intro u hu hf1
            sorry











        | negation f =>
            constructor
            intro h2
            simp at hc
            have hp2:n ≥ f.size:= by linarith
            unfold Formula.force_form at h2
            have hpn:=hn f hp2
            apply (closed h0).mpr


            sorry
            intro h2
            have h2:=(closed h0).mp h2
            unfold Formula.force_form
            intro Mw re cond
            sorry




        | existential_quantification f =>
          constructor
          intro h2
          sorry
          intro h4
          have h3:=h0.right.right.right f h4
          unfold Formula.force_form
          rcases h3 with ⟨c,hx⟩
          use (val0 (@Term.const σ c))
          generalize eq:(Formula.down 1 0 (Formula.Substitution f (Term.free (free_variable.free_variable 0)) (Term.const c)))=p
          have hp1:Formula.size p = Formula.size f:=by rw[← eq];simp;
          simp at hc
          have hp2:n ≥ p.size:= by linarith
          have hp3:=hn p hp2
          rw[eq] at hx
          have hx1:=hp3.mpr hx
          rw[← eq] at hx1
          sorry














            | universal_quantification f =>
              constructor
              intro h2
              simp at hc
              have hp2:n ≥ f.size:= by linarith
              have hp3:=hn f hp2
              apply (closed h0).mpr
              unfold Formula.force_form at h2

              sorry
              intro h4
              simp at hc
              have hp2:n ≥ f.size:= by linarith
              -- have hp3:=hn f hp2
              unfold Formula.force_form
              have h4:=(closed h0).mp h4
              intro t
              have xterm:= @Encodable.decode (Term σ) _ t
              

              sorry



lemma model_tt_iff_mem{p : Formula σ}{w: Set (Formula σ)}(h0:w ∈ M.W ) :
  (Formula.force_form M w h0 val0 p) ↔ (p ∈ w) := by sorry



lemma model_tt_iff_prf {p : Formula σ}(h0:w ∈ M.W ) :
  (Formula.force_form M w h0 val0 p) ↔ (w ⊢ p) := by
  apply Iff.trans (model_tt_iff_mem h0)
  apply Iff.trans (closed h0)
  rfl





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

  intro f hpm
  have h2: f ∈ prime Γ p := subset_prime_self hpm
  have h3:= Proof.ref h2
  apply (model_tt_iff_prf hd).mpr h3
  intro x
  have h2:=(model_tt_iff_prf hd).mp x
  have h1:=prime_no_prf h.right
  trivial
