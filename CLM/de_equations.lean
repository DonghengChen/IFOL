import CLM.IFOL
open IFOL
open Classical

lemma down_free(σ:Signature)(h:m>0) :(Term.down 0 (@Term.free σ m))=Term.free (m-1):= by
  simp[Term.down]

lemma down_const(σ:Signature)(m): (Term.down 0 (@Term.const σ m))=Term.const m:= by
  simp[Term.down]

lemma down_lift(σ:Signature)(t): (Term.down 0 (@Term.lift σ 0 t))=t:= by
  cases t<;>simp[Term.lift,Term.down]


def down_insert {σ:Signature}{M:model σ}{val0: (Term σ) → M.A}{f:Formula σ}{xterm:Term σ}{t:M.A}(heq: val0 xterm = t):
∀(h0: M.world),(hz:h0 ∈ M.W) → (Formula.force_form M h0 hz val0 (Formula.down 0 (Formula.Substitution f (Term.free 0) (Term.lift 0 xterm)))) ↔
 (Formula.force_form M h0 hz (insert_value_function M val0 t) f) := by
  induction f generalizing val0 xterm t with
  | atomic_formula r ts=> intro h0 hz;constructor
                          intro h
                          simp [Formula.force_form] at h
                          simp [Formula.force_form, insert_value_function]
                          generalize eq: model.α M h0 r =fx
                          rw [eq] at h
                          have h1: ∀x y, (fx x) → x = y → fx y := by intros x y h1 h2; rw [← h2]; exact h1
                          have h2: ∀x y, x = y → (val0 x = val0 y):= by intros x y z; rw [z]
                          apply h1 _ _ h
                          funext X
                          rw [← heq]
                          cases (ts X) with
                          | free n=> simp;
                                     by_cases h1:(n=0)
                                     simp [h1]
                                     apply h2
                                     simp [Term.Substitution]
                                     apply down_lift
                                     simp [h1]
                                     apply h2
                                     simp [Term.Substitution,h1]
                                     apply down_free
                                     positivity
                          | const n=> simp[Term.Substitution,down_const]
                          intro h
                          simp [Formula.force_form] at h
                          simp [Formula.force_form, insert_value_function]
                          generalize eq: model.α M h0 r =fx
                          rw [eq] at h
                          have h1: ∀x y, (fx x) → x = y → fx y := by intros x y h1 h2; rw [← h2]; exact h1
                          have h2: ∀x y, x = y → (val0 x = val0 y):= by intros x y z; rw [z]
                          apply h1 _ _ h
                          funext X
                          rw [← heq]
                          cases (ts X) with
                          | free n=>
                                     simp [Term.Substitution,insert_value_function]
                                     by_cases h1:(n=0)
                                     simp[h1,down_lift]
                                     simp[h1]
                                     rw[down_free]
                                     positivity

                          | const n=> simp[Term.Substitution,insert_value_function,down_const]

   | conjunction f1 f2 h1 h2=>
      intro h0 hz
      constructor;intro h
      simp [Formula.Substitution,Formula.down,Formula.force_form] at h
      have h11:=(h1 heq _ _).mp h.left
      have h22:=(h2 heq _ _).mp h.right
      simp [Formula.force_form]
      exact ⟨h11,h22⟩
      intro h
      simp [Formula.Substitution,Formula.down,Formula.force_form] at h
      have h11:=(h1 heq _ _).mpr h.left
      have h22:=(h2 heq _ _).mpr h.right
      simp [Formula.force_form]
      exact ⟨h11,h22⟩
   | disjunction f1 f2 h1 h2=>
      intro h0 hz
      constructor;intro h
      simp [Formula.Substitution,Formula.down,Formula.force_form] at h
      cases h with
      | inl h0=> exact (Or.inl ((h1 heq _ _).mp h0))
      | inr h0=> exact (Or.inr ((h2 heq _ _).mp h0))
      intro h
      simp [Formula.Substitution,Formula.down,Formula.force_form] at h
      cases h with
      | inl h0=> exact (Or.inl ((h1 heq _ _).mpr h0))
      | inr h0=> exact (Or.inr ((h2 heq _ _).mpr h0))
   | bottom => intro h0 hz;constructor<;>intro h<;>simp [Formula.Substitution,Formula.down,Formula.force_form] at h
   | implication f1 f2 h1 h2=>
      intro h0 hz
      constructor;intro h
      simp [Formula.Substitution,Formula.down,Formula.force_form] at h
      simp [Formula.force_form]
      intro u hu
      have h3:= h u hu
      intro hx
      have huu:=M.R_closed h0 u hu hz
      apply (h2 heq u huu).mp
      apply h3
      apply (h1 heq u huu).mpr
      exact hx
      intro h
      simp [Formula.Substitution,Formula.down,Formula.force_form]
      intro u hu
      have huu:=M.R_closed h0 u hu hz
      intro hx
      apply (h2 heq u huu).mpr
      have h3:= h u hu
      apply h3
      apply (h1 heq u huu).mp
      exact hx
   | existential_quantification f hf=>
      intro h0 hz
      constructor;intro h
      unfold Formula.force_form
      simp [Formula.Substitution,Formula.down,Formula.force_form] at h
      cases h;rename_i tt ht
      use tt

      sorry
      intro h
      simp [Formula.Substitution,Formula.down,Formula.force_form]
      simp [Formula.force_form] at h
      cases h;rename_i tt ht
      use tt
      sorry

















   | universal_quantification f hf=>
      intro h0 hz
      constructor
      intro h
      unfold Formula.force_form
      simp [Formula.Substitution,Formula.down,Formula.force_form] at h
      intro t;have h:=h t;rename_i tt ttt
      sorry
      intro h
      simp [Formula.Substitution,Formula.down,Formula.force_form]
      simp [Formula.force_form] at h
      intro t;have h:=h t;rename_i tt ttt
      sorry
