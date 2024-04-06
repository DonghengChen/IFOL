import CLM.IFOL
import CLM.encode_formula
import CLM.general
open IFOL
open Set
open Classical

def p_bot_form {σ:Signature}(p : (Formula σ))(n:ℕ): (Formula σ) :=
  match n with
  | 0 => p
  | (n+1) => p_bot_form p n ∨ᵢ ⊥

def qp_bot_form{σ:Signature}(q p : (Formula σ))(n:ℕ): (Formula σ) :=
q ∨ᵢ p_bot_form p n

def pq_bot_form{σ:Signature}(p q : (Formula σ))(n:ℕ): (Formula σ) :=
(p_bot_form p n) ∨ᵢ q

def e_bot_form{σ:Signature}(p : (Formula σ))(n:ℕ): (Formula σ) :=
∃ᵢ p_bot_form p n

theorem size_p_bot{σ:Signature}(p : (Formula σ))(n:ℕ): Formula.size (p_bot_form p n) = Formula.size p + n := by
induction n with
  | zero => rfl
  | succ n ih => simp [p_bot_form, Formula.size]
                 rw[ih]
                 linarith

theorem size_qp_bot{σ:Signature}(q p: (Formula σ))(n:ℕ): Formula.size (qp_bot_form q p n) = Formula.size p + n + 1 + Formula.size q:= by
simp
rw [size_p_bot]
linarith


theorem provable_p_bot{σ:Signature}(Γ : Set (Formula σ))(p : (Formula σ))(n:ℕ): (Γ ⊢ p_bot_form p n) ↔ (Γ ⊢ p) := by
induction n with
  | zero => simp [p_bot_form]
  | succ n ih => simp [p_bot_form]
                 rw[←ih]
                 constructor
                 intro h0
                 rw[← union_self Γ]
                 nth_rw 1 [← union_self Γ]
                 apply Proof.elimO h0
                 apply Proof.ref
                 simp
                 apply Proof.botE
                 apply Proof.ref
                 simp

                 intro h0
                 apply Proof.introO1
                 exact h0

theorem provable_e_bot{σ:Signature}(Γ : Set (Formula σ))(p : (Formula σ))(n:ℕ): (Γ ⊢ e_bot_form p n) ↔ (Γ ⊢ ∃ᵢ p) := by
simp[e_bot_form]
sorry



theorem provable_qp_bot{σ:Signature}(Γ : Set (Formula σ))(q p : (Formula σ))(n:ℕ):(Γ ⊢ qp_bot_form q p n) ↔ (Γ ⊢ q ∨ᵢ p) := by
simp[qp_bot_form]
constructor
intro hl
rw[← union_self Γ]
nth_rw 1 [← union_self Γ]
apply Proof.elimO hl
apply Proof.introO1
apply Proof.ref;simp
apply Proof.introO2
suffices h0:{p_bot_form p n}⊢p
apply subset_proof h0;simp
have h1:{p_bot_form p n}⊢p_bot_form p n:= by apply Proof.ref;simp
apply (provable_p_bot {p_bot_form p n} p n).mp h1

intro hr
rw[← union_self Γ]
nth_rw 1 [← union_self Γ]
apply Proof.elimO hr
apply Proof.introO1
apply Proof.ref;simp
apply Proof.introO2
have h1:{p}⊢p:=by apply Proof.ref;simp
have h0:{p}⊢p_bot_form p n:= by apply (provable_p_bot {p} p n).mpr h1
apply subset_proof h0
simp



theorem inf_form_gen{σ:Signature}(p q : (Formula σ))(n:ℕ):∃m, n ≤ (@Encodable.encode (Formula σ) _ (qp_bot_form q p m)) := by
  by_contra h0
  push_neg at h0
  let mapFin:ℕ → Fin n := fun n=> ⟨Encodable.encode (qp_bot_form q p n),h0 n⟩
  have h1:=Finite.exists_ne_map_eq_of_infinite mapFin
  rcases h1 with ⟨x,y,hneq,hxy⟩
  simp at hxy
  have h2:Formula.size (qp_bot_form q p x) = Formula.size (qp_bot_form q p y):=by rw[hxy]
  simp [size_p_bot] at h2
  exact hneq h2

theorem inf_form_gen2{σ:Signature}(p q : (Formula σ))(n:ℕ):∃m, n ≤ (@Encodable.encode (Formula σ) _ (pq_bot_form p q m)) := by
  by_contra h0
  push_neg at h0
  let mapFin:ℕ → Fin n := fun n=> ⟨Encodable.encode (pq_bot_form p q n),h0 n⟩
  have h1:=Finite.exists_ne_map_eq_of_infinite mapFin
  rcases h1 with ⟨x,y,hneq,hxy⟩
  simp at hxy
  have h2:Formula.size (pq_bot_form p q x) = Formula.size (pq_bot_form p q y):=by rw[hxy]
  simp [size_p_bot] at h2
  exact hneq h2

theorem inf_form_gene{σ:Signature}(p : (Formula σ))(n:ℕ):∃m, n ≤ (@Encodable.encode (Formula σ) _ (e_bot_form p m)) := by
  by_contra h0
  push_neg at h0
  let mapFin:ℕ → Fin n := fun n=> ⟨Encodable.encode (e_bot_form p n),h0 n⟩
  have h1:=Finite.exists_ne_map_eq_of_infinite mapFin
  rcases h1 with ⟨x,y,hneq,hxy⟩
  simp at hxy
  have h2:Formula.size (e_bot_form p x) = Formula.size (e_bot_form p y):=by rw[hxy]
  simp [size_p_bot] at h2
  exact hneq h2


lemma p_bot_form_cross_sub{σ:Signature}{p : (Formula σ)}{n:ℕ}{s t:Term σ}: (p_bot_form (Formula.Substitution p s t) n) = Formula.Substitution (p_bot_form p n) s t := by
    induction n
    simp[p_bot_form,Formula.Substitution]
    rename_i n hn
    simp[p_bot_form,hn]
    rw[← hn]
    generalize eq:(p_bot_form (Formula.Substitution p s t) n∨ᵢ⊥) = q
    unfold Formula.Substitution
    simp
    cases s
    simp[Formula.Substitution]
    rw [← eq]
    simp
    exact hn
    simp[Formula.Substitution]
    rw [← eq]
    simp
    exact hn

lemma p_bot_form_cross_lift{σ:Signature}{p : (Formula σ)}{n k:ℕ}: (p_bot_form (Formula.lift k p) n) = Formula.lift k (p_bot_form p n) := by
    induction n
    simp[p_bot_form,Formula.lift]
    rename_i n hn
    simp[p_bot_form,hn]
    rw[← hn]
    generalize eq:(p_bot_form (Formula.lift k p) n∨ᵢ⊥) = q
    unfold Formula.lift
    simp[Formula.lift]
    rw [← eq]
    simp
    exact hn

lemma p_bot_form_cross_down{σ:Signature}{p : (Formula σ)}{n k:ℕ}: (p_bot_form (Formula.down k p) n) = Formula.down k (p_bot_form p n) := by
    induction n
    simp[p_bot_form,Formula.down]
    rename_i n hn
    simp[p_bot_form,hn]
    rw[← hn]
    generalize eq:(p_bot_form (Formula.down k p) n∨ᵢ⊥) = q
    unfold Formula.down
    simp[Formula.down]
    rw [← eq]
    simp
    exact hn
