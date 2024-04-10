import CLM.completeness
import CLM.bijection
-- import CLM.de_equations
open IFOL

def is_consist(Γ :  Set (Formula σ)) :=  ¬ (Γ ⊢ ⊥)

def worlds: Set (Set (Formula σ)) := {w: Set (Formula σ)| is_consist w ∧is_prime w}





lemma consist_of_not_prf {Γ :  Set (Formula σ)} {p : Formula σ} :
  ¬ (Γ ⊢ p) → is_consist Γ := fun x y=>x (Proof.botE p y)
namespace canonical

@[simp]
def M {σ : Signature} : model (σ) where
  world := Set (Formula σ)
  W := worlds
  A := ℕ
  R := λ w v=> (w ⊆ v) ∧ v ∈ worlds
  α := fun w r map =>
    @Formula.atomic_formula σ r (fun x=> @det σ (map x))∈ w
  refl := λ w v => by simp;constructor;rfl;exact v
  R_closed := λ w v v' h => by simp at v';exact v'.2
  trans := λ w v v' v'' h1 h2 => by simp; intro h3 h4 h5 h6;constructor;exact Set.Subset.trans h3 h5;exact h6
  mono := by
    intro u v hu hv r ts huv hn
    have h1:= huv.left hn
    exact h1



def val0 {σ: Signature} (t: Term σ) : ℕ := ent t


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




lemma model_tt_iff_mem_p (n:Nat):
  ∀w: Set (Formula σ),∀(p : Formula σ),(n≥p.size) → (h: w ∈ M.W) →  ((Formula.force_form M w h val0 p) ↔ (w ⊢ p)) := by
  induction n
  intro h0 p hc
  case zero => simp at hc
               unfold Formula.size at hc
               cases p with
               | atomic_formula r ts=>  intro h0
                                        constructor
                                        intro hw
                                        unfold Formula.force_form at hw
                                        simp at hw
                                        unfold val0 at hw
                                        simp [de_bij] at hw
                                        apply (closed h0).mp
                                        exact hw
                                        intro hp
                                        unfold Formula.force_form
                                        simp
                                        unfold val0
                                        simp [de_bij]
                                        apply (closed h0).mpr
                                        exact hp
                | conjunction f1 f2  => simp at hc
                | disjunction f1 f2  => simp at hc
                | implication f1 f2  => simp at hc
                | existential_quantification f  => simp at hc
                | universal_quantification f  => simp at hc
                | bottom =>
                  simp at hc
                  unfold Formula.force_form
                  intro h0
                  constructor
                  intro h;trivial
                  simp at h0
                  intro h
                  unfold worlds at h0
                  have h1:=h0.left
                  apply h1
                  exact h




  case succ n hn =>
        intro h0 p hc
        cases p with
        | bottom =>
          unfold Formula.force_form
          intro h0
          constructor
          intro h;trivial
          simp at h0
          intro h
          unfold worlds at h0
          have h1:=h0.left
          apply h1
          exact h
        | atomic_formula r ts=>
          intro h0
          constructor
          intro hw
          unfold Formula.force_form at hw
          simp at hw
          unfold val0 at hw
          simp [de_bij] at hw
          apply (closed h0).mp
          exact hw
          intro hp
          unfold Formula.force_form
          simp
          unfold val0
          simp [de_bij]
          apply (closed h0).mpr
          exact hp

        | conjunction f1 f2 =>

          simp at hc
          have h01:n ≥ f1.size:= by linarith
          have h02:n ≥ f2.size:= by linarith
          have h1:=hn h0 f1 h01
          have h2:=hn h0 f2 h02
          intro h0
          constructor
          intro h
          unfold Formula.force_form at h
          have h1:= ((h1 h0).mp h.left)
          have h2:= ((h2 h0).mp h.right)
          have h3:= Proof.introA h1 h2
          rw [Set.union_self] at h3
          exact h3
          intro h
          have h3:=Proof.elimA1 h
          have h4:=Proof.elimA2 h
          have h3:=(h1 h0).mpr h3
          have h4:=(h2 h0).mpr h4
          constructor
          exact h3
          exact h4

        | disjunction f1 f2=>
          simp at hc
          have h01:n ≥ f1.size:= by linarith
          have h02:n ≥ f2.size:= by linarith
          have h1:=hn h0 f1 h01
          have h2:=hn h0 f2 h02
          intro h0
          constructor
          intro h
          simp at h0
          unfold Formula.force_form at h
          cases h with
          | inl ht=>have h1:=(h1 h0).mp ht;exact (Proof.introO1 _ h1)
          | inr ht=>have h2:=(h2 h0).mp ht;exact (Proof.introO2 _ h2)
          intro h
          simp at h0
          have h0:=h0.right.right.left f1 f2 ((closed h0).mpr h)
          unfold Formula.force_form
          cases h0 with
          | inl ht=>left; exact (h1 h0).mpr ((closed h0).mp ht)
          | inr ht=>right; exact (h2 h0).mpr ((closed h0).mp ht)

        | implication f1 f2 =>
            simp at hc
            have h01:n ≥ f1.size:= by linarith
            have h02:n ≥ f2.size:= by linarith
            have h1:=hn h0 f1 h01
            have h2:=hn h0 f2 h02
            intro hw
            constructor
            intro h
            unfold Formula.force_form at h
            have hr: model.R M h0 h0 := by simp;constructor;rfl;simp at hw;exact hw
            have hz:=h h0 hr
            rw [h1,h2] at hz
            by_cases hc1:(h0⊢f1)
            apply Proof.introI
            apply cond_mono_proof2
            exact hz hc1
            let w2:M.world:=by simp;exact (h0∪{f1})
            apply Proof.introI
            by_contra z
            have ht:= prime_no_prf z
            suffices h3p:prime (h0 ∪ {f1}) f2 ∈ M.W
            have h4: h0 ⊆ prime (h0 ∪ {f1}) f2 := by simp[prime];apply Set.subset_union_of_subset_left;simp
            have h5: M.R h0 (prime (h0 ∪ {f1}) f2) := by constructor;exact h4;simp at h3p;simp;exact h3p
            have h6:= h (prime (h0 ∪ {f1}) f2) h5
            have hp1:=hn (prime (h0 ∪ {f1}) f2) f1 h01 h3p
            have hp2:=hn (prime (h0 ∪ {f1}) f2) f2 h02 h3p
            rw[hp1] at h6
            rw[hp2] at h6
            apply ht

            apply h6
            have h10:(h0 ∪ {f1}) ⊢ f1 := by apply Proof.ref;simp
            apply subset_proof h10
            apply Set.subset_union_of_subset_left;
            rfl
            constructor
            simp only[is_consist]
            intro hbot
            apply ht
            apply Proof.botE
            exact hbot
            apply prime_of_prime

            intro h
            simp [Formula.force_form]
            intro u hu hf1
            have h1:=hn u f1 h01 hu.2
            have h2:=hn u f2 h02 hu.2
            rw[h2]
            rw[h1] at hf1
            have hh: u ⊢ f1→ᵢf2:= by apply subset_proof h;simp at hu;exact hu.left
            rw[← Set.union_self u]
            apply Proof.elimI hh hf1


























        | existential_quantification f =>
          intro ht
          constructor
          intro h2




          unfold Formula.force_form at h2
          rcases h2 with ⟨t,hx⟩
          generalize eq2: @det σ t = xterm
          have eq3: val0 (xterm) = t := by rw[← eq2];simp[val0];simp[ed_bij]
          have h9:=@down_insert σ M val0 f xterm t eq3 h0 ht
          have h8:=h9.mpr hx
          generalize eq4:(Formula.down 0 (Formula.Substitution f (Term.free 0) (Term.lift 0 xterm))) = g
          rw[eq4] at h8
          simp at hc
          have h7: n ≥ g.size := by rw[← eq4];simp;linarith
          have h6:=hn g h7 ht
          rw [← eq4] at h8
          generalize eq5: (Formula.down 0 (Formula.Substitution f (Term.free 0)
                       (Term.lift 0 xterm))) = gg
          generalize eq6 : (gg.Substitution (Term.free 0) (Term.free 0))=gh
          have h99: Formula.force_form M h0 ht val0 gh:=sorry
          have hgh: n ≥ Formula.size gh:=by rw[←eq6];simp;rw[←eq5];simp;linarith
          have h100:=(hn gh hgh ht).mp h99
          have h101:=(closed ht).mp h100
          rw [← eq6] at h101
          have h100:=Proof.introE h101
          simp [Term.lift] at h100




          have h5:= Proof.introE h8









          intro h4
          have h3:=ht.right.right.right f h4
          unfold Formula.force_form
          rcases h3 with ⟨c,hx⟩
          use (val0 (@Term.const σ c))
          generalize eq:(Formula.down 0 (Formula.Substitution f (Term.free 0) (Term.const c)))=p
          have hp1:Formula.size p = Formula.size f:=by rw[← eq];simp;
          simp at hc
          have hp2:n ≥ p.size:= by linarith
          have hp3:=hn p hp2
          rw[eq] at hx
          have hx1:=(hp3 ht).mpr hx
          rw[← eq] at hx1
          generalize eq3:  (Term.const c) = xterm
          generalize eq2: val0 (xterm) = t
          have q:=(@down_insert σ M val0 f xterm t eq2 h0 ht)
          apply q.mp
          rw[← eq3]
          simp[Term.lift]
          exact hx1
















            | universal_quantification f =>
              intro hz
              constructor
              intro h2
              simp at hc
              have hp2:n ≥ f.size:= by linarith
              have hp3:=hn h0 f hp2
              unfold Formula.force_form at h2

              sorry
              intro h4
              simp at hc
              have hp2:n ≥ f.size:= by linarith
              -- have hp3:=hn f hp2
              unfold Formula.force_form
              have h4:=(closed hz).mp h4
              intro t
              simp at t
              let xterm:= @det σ t
              have h5:= Proof.elimF xterm h4
              have h6: (Formula.down 0 (Formula.Substitution f (Term.free 0) (Term.lift 0 xterm))).size = f.size := by simp
              rw [← h6] at hp2
              have h7:= hn (Formula.down 0 (Formula.Substitution f (Term.free 0) (Term.lift 0 xterm))) hp2 hz
              have h8:= (closed hz).mpr h5
              have h9:= h7.mpr h8
              have eq3: val0 (xterm) = t := by simp[val0];simp[ed_bij]
              have h10:=@down_insert σ M val0 f xterm t eq3 h0 hz
              have h11:=h10.mp h9
              exact h11



















lemma model_tt_iff_prf {p : Formula σ}(h0:w ∈ M.W ):
  (Formula.force_form M w h0 val0 p) ↔ (w ⊢ p) := by
  apply ( model_tt_iff_mem_p p.size )
  rfl




theorem completeness {Γ :  Set (Formula σ)} {p : Formula σ}(hstd: std Γ p) :
  (Γ ⊧ p) → (Γ ⊢ p) := by
  by_contra h;push_neg at h;
  have hd: (prime Γ p ) ∈ worlds := by
    constructor
    apply consist_of_not_prf
    exact prime_no_prf h.right hstd
    exact prime_of_prime
  apply absurd
  fapply h.left
  exact M
  exact prime Γ p
  exact val0
  exact hd

  intro f hpm
  have h2: f ∈ prime Γ p := by simp;left;exact hpm
  have h3:= Proof.ref h2
  apply (model_tt_iff_prf hd hstd).mpr h3
  intro x
  have h2:=(model_tt_iff_prf hd).mp x
  have h1:=prime_no_prf h.right hstd
  trivial
