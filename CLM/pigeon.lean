import CLM.IFOL
import CLM.encode_formula
import CLM.proof_lemmas
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

theorem provable_p_bot{σ:Signature}(Γ : Set (Formula σ))(p : (Formula σ))(n:ℕ): (Γ ⊢ p_bot_form p n) ↔ (Γ ⊢ p) := by
induction n with
  | zero => simp [p_bot_form]
  | succ n ih => simp [p_bot_form]
                 rw[←ih]
                 constructor
                 intro h0
                 apply Proof.elimO h0
                 apply Proof.ref
                 simp
                 apply Proof.botE
                 apply Proof.ref
                 simp

                 intro h0
                 apply Proof.introO1
                 exact h0

-- `provable_e_bot` is proved in `henkin.lean` (it needs a fresh Henkin
-- constant, i.e. the `set_max`/`no_const_max` machinery defined there).

lemma inst_or{σ:Signature}{f1 f2 : Formula σ}{s : Term σ}:
    Formula.inst (f1 ∨ᵢ f2) s = ((Formula.inst f1 s) ∨ᵢ (Formula.inst f2 s)) := by
  simp [Formula.inst, Formula.Substitution, Formula.down]

lemma inst_bot{σ:Signature}{s : Term σ}:
    Formula.inst (Formula.bottom : Formula σ) s = Formula.bottom := by
  simp [Formula.inst, Formula.Substitution, Formula.down]

lemma p_bot_cross_inst{σ:Signature}{p : (Formula σ)}{n:ℕ}{s:Term σ}:
    (p_bot_form (Formula.inst p s) n) = Formula.inst (p_bot_form p n) s := by
  induction n with
  | zero => rfl
  | succ n hn => simp [p_bot_form, inst_or, inst_bot, hn]

lemma ft_p_bot{σ:Signature}(p : Formula σ)(n b : ℕ) :
    Formula.free_terms (p_bot_form p n) b = Formula.free_terms p b := by
  induction n with
  | zero => rfl
  | succ n ih => simp [p_bot_form, Formula.free_terms, ih]



theorem provable_qp_bot{σ:Signature}(Γ : Set (Formula σ))(q p : (Formula σ))(n:ℕ):(Γ ⊢ qp_bot_form q p n) ↔ (Γ ⊢ q ∨ᵢ p) := by
simp[qp_bot_form]
constructor
intro hl
apply Proof.elimO hl
apply Proof.introO1
apply Proof.ref;simp
apply Proof.introO2
suffices h0:{p_bot_form p n}⊢p
apply subset_proof h0;simp
have h1:{p_bot_form p n}⊢p_bot_form p n:= by apply Proof.ref;simp
apply (provable_p_bot {p_bot_form p n} p n).mp h1

intro hr
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


