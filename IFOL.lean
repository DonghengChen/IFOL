import Mathlib.Init.Set
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Data.Set.Basic
open Set



structure Signature where
  (function_symbols : Type)
  (relation_symbols : Type)
  (arity : function_symbols → Nat)
  (arity' : relation_symbols → Nat)

inductive term (σ : Signature): Type
| free_variable : Nat → term σ
-- | function_application (f : σ.function_symbols) : (Fin (σ.arity f) → term σ ) → term σ
| Constant : Nat → term σ --constant is key word in Lean 4
-- | relation_application (r : σ.relation_symbols) : (Fin (σ.arity' r) → term σ )

inductive formula (σ : Signature) : Type
| atomic_formula : (r : σ.relation_symbols) → (Fin (σ.arity' r) → term σ ) → formula σ
| conjunction : formula σ → formula σ → formula σ
| disjunction : formula σ → formula σ → formula σ
| existential_quantification : formula σ → formula σ
| universal_quantification :  formula σ → formula σ
| implication : formula σ → formula σ → formula σ
| bottom : formula σ
| negation : formula σ → formula σ


def term_eql {σ : Signature} :term σ → term σ → Prop := fun t1 => fun t2 =>by
cases t1 with
| free_variable n => cases t2 with
  |free_variable m => exact n=m
  |Constant _ => exact False
| Constant n=> cases t2 with
  |free_variable _ => exact False
  | Constant m => exact n=m



notation "⊥" => formula.bottom
infixr:50 "→ᵢ" => formula.implication
infixr:40 "∧ᵢ" => formula.conjunction
infixr:30 "∨ᵢ" => formula.disjunction
prefix:25 "∃ᵢ" => formula.existential_quantification
prefix:24 "∀ᵢ" => formula.universal_quantification
prefix:19 "#" => formula.atomic_formula
prefix:20 "¬ᵢ" => formula.negation


def term_lift{σ : Signature}: ℤ → Nat → term σ → term σ := --i c n → n
fun i => fun c=> fun t=> by
cases t with
| free_variable n =>
exact if n < c then (term.free_variable n) else term.free_variable (n+i)
-- | function_application f ts => exact term.function_application f (fun q:Fin (σ.arity f)=> term_lift i c (ts q))
| Constant n => exact term.Constant n

def formula_lift{σ : Signature}: ℤ → Nat → formula σ → formula σ  :=
fun i => fun c => fun f => by
cases f with
| atomic_formula r ts => exact formula.atomic_formula r (fun q:Fin (σ.arity' r)=> term_lift i c (ts q))
| conjunction f1 f2 => exact (formula_lift i c f1) ∧ᵢ (formula_lift i c f2)
| disjunction f1 f2 => exact (formula_lift i c f1) ∨ᵢ (formula_lift i c f2)
| implication f1 f2 => exact (formula_lift i c f1) →ᵢ (formula_lift i c f2)
| bottom  => exact ⊥
| negation f => exact ¬ᵢ (formula_lift i c f)
| existential_quantification f => exact ∃ᵢ (formula_lift i (c+1) f)
| universal_quantification f => exact ∀ᵢ (formula_lift i (c+1) f)




def term_subsitution{σ : Signature}: term σ → term σ → term σ → term σ  :=by
intro src m e
cases src with
| free_variable n => cases m with
  |free_variable n' => exact if n=n' then e else term.free_variable n
  |Constant _ => exact term.free_variable n
| Constant n=> cases m with
  |free_variable _ => exact term.Constant n
  | Constant n' => exact if n=n' then e else term.free_variable n

def depth {σ : Signature}: formula σ → Nat :=
fun f => by
cases f with
| atomic_formula r ts=> exact 0
| bottom  => exact 0
| negation f => exact depth f
| existential_quantification f => exact (depth f)+1
| universal_quantification f=> exact (depth f)+1
| conjunction f1 f2=> exact max (depth f1) (depth f2)
| disjunction f1 f2=> exact max (depth f1) (depth f2)
| implication f1 f2=> exact max (depth f1) (depth f2)

def formula_subsitution{σ : Signature}: formula σ → term σ  → term σ → formula σ :=
fun f => fun m =>fun e => by
cases m with
| Constant t =>
  cases f with
  | atomic_formula r ts => exact (# r) (fun q:Fin (σ.arity' r)=> term_subsitution (ts q) (term.Constant t) e)
  | conjunction f1 f2 => exact (formula_subsitution f1 (term.Constant t)  e) ∧ᵢ (formula_subsitution f2 (term.Constant t) e)
  | disjunction f1 f2 => exact (formula_subsitution f1 (term.Constant t)  e) ∨ᵢ (formula_subsitution f2 (term.Constant t) e)
  | implication f1 f2 => exact (formula_subsitution f1 (term.Constant t)  e) →ᵢ (formula_subsitution f2 (term.Constant t) e)
  | bottom  => exact ⊥
  | negation f => exact ¬ᵢ (formula_subsitution f (term.Constant t) e)
  | existential_quantification f => exact ∃ᵢ(formula_subsitution f (term.Constant t) e)
  | universal_quantification f => exact ∀ᵢ (formula_subsitution f (term.Constant t) e)
| free_variable t =>
  cases f with
  | atomic_formula r ts => exact (# r) (fun q:Fin (σ.arity' r)=> term_subsitution (ts q) (term.free_variable t) e)
  | bottom  => exact ⊥
  | negation f => exact ¬ᵢ (formula_subsitution f (term.free_variable t) e)
  | existential_quantification f => exact ∃ᵢ(formula_subsitution f (term.free_variable t) e)
  | universal_quantification f => exact ∀ᵢ (formula_subsitution f (term.free_variable t) e)
  | conjunction f1 f2 => let (top:ℕ)  := (max (depth f1) (depth f2) )
                         exact (formula_subsitution f1 (term.free_variable (t+(depth f1) - top)) e) ∧ᵢ (formula_subsitution f2 (term.free_variable  (t+(depth f2) - top)) e)
  | disjunction f1 f2 => let (top:ℕ)  := (max (depth f1) (depth f2) )
                         exact (formula_subsitution f1 (term.free_variable (t+(depth f1) - top)) e) ∨ᵢ (formula_subsitution f2 (term.free_variable  (t+(depth f2) - top)) e)
  | implication f1 f2 => let (top:ℕ)  := (max (depth f1) (depth f2) )
                         exact (formula_subsitution f1 (term.free_variable (t+(depth f1) - top)) e)  →ᵢ (formula_subsitution f2 (term.free_variable  (t+(depth f2) - top)) e)



def β_reduction{σ : Signature}: formula σ → term σ → formula σ :=
fun f => fun t => by
cases f with
| atomic_formula r ts=> exact (# r) ts
| conjunction f1 f2 =>exact  f1 ∧ᵢ f2
| disjunction f1 f2 =>exact f1 ∨ᵢ f2
| implication f1 f2 => exact f1 →ᵢ f2
| bottom  => exact ⊥
| negation f => exact ¬ᵢ f
| existential_quantification f => exact formula_lift (-1) 0 (formula_subsitution f (term.free_variable 0) (term_lift 1 0 t))
| universal_quantification f =>  exact formula_lift (-1) 0 (formula_subsitution f (term.free_variable 0) (term_lift 1 0 t))




def free_variables_term {σ : Signature} : term σ → Nat → Set Nat
| term.free_variable x => fun bound => if x>= bound then {x} else ∅
| term.Constant _=> fun _ =>∅
-- | term.function_application f ts => ⋃ (i:Fin (σ.arity f)),free_variables_term (ts i)

def free_variables_formula {σ : Signature} : formula σ → Nat → Set Nat
| formula.atomic_formula r ts=>fun bound=> ⋃ (i:Fin (σ.arity' r)),free_variables_term (ts i) bound
| formula.negation f => fun bound=> free_variables_formula f bound
-- | formula.equalities t1 t2=> (free_variables_term t1).union (free_variables_term t2)
| formula.bottom =>fun _ => ∅
| formula.conjunction f1 f2 => fun bound =>(free_variables_formula f1 bound).union (free_variables_formula f2 bound)
| formula.disjunction f1 f2 => fun bound =>(free_variables_formula f1 bound).union (free_variables_formula f2 bound)
| formula.implication f1 f2 => fun bound =>(free_variables_formula f1 bound).union (free_variables_formula f2 bound)
| formula.existential_quantification f =>fun bound => free_variables_formula f (bound+1)
| formula.universal_quantification f => fun bound => free_variables_formula f (bound+1)

def free_variables_set {σ : Signature} : Set (formula σ) → Set Nat:=
fun Γ => ⋃ (f ∈ Γ), free_variables_formula f 0



inductive proof {σ : Signature} : Set (formula σ) → formula σ → Type
| ref {Γ} {A} (h : A ∈ Γ) : proof Γ A
| introI {Γ} (A B) (h: (proof (Γ∪{A}) B)): proof Γ (A →ᵢ B)
| elimI {Γ Q} {A B} (h1: (proof Γ (A →ᵢ B)))(h2: (proof Q A)): proof (Γ ∪ Q) B
| introA {Γ Q} {A B} (h1: proof Γ A)(h2: proof Q B): proof (Γ ∪ Q) (A ∧ᵢ B)
| elimA1 {Γ} {A B} (h: proof Γ (A ∧ᵢ B)): proof Γ A
| elimA2 {Γ} {A B} (h: proof Γ (A ∧ᵢ B)): proof Γ B
| introO1 {Γ} {A B} (h: proof Γ A): proof Γ (A ∨ᵢ B)
| introO2 {Γ} {A B} (h: proof Γ B): proof Γ (A ∨ᵢ B)
| elimO {Γ Q} {A B C} (h1: proof Γ (A ∨ᵢ B))(h2: proof (Γ ∪ {A}) C)(h3: proof (Γ ∪ {B}) C): proof (Γ ∪ Q) C
| introN {Γ Q}{A B}(h1: proof (Γ∪{A}) B)(h2: proof (Q∪{A}) (¬ᵢB)):proof (Γ ∪ Q) (¬ᵢA)
| ine {Γ}{A B}(h1: proof Γ A)(h2: proof Γ  (¬ᵢA)):proof Γ B
| introF {Γ}{A}(h1:proof Γ A)(x:Nat)(h2: x ∉ (free_variables_set Γ)): proof Γ (∀ᵢ (formula_subsitution A (term.free_variable x) (term.free_variable (depth A))))
| elimF {Γ}{A}(h:proof Γ (∀ᵢ A))(τ: term σ):proof Γ (formula_lift (-1) 0 (formula_subsitution f (term.free_variable 0) (term_lift 1 0 τ)))
| introE {Γ}{A}(t: term σ)(h: proof Γ A ): proof Γ (∃ᵢ formula_subsitution A t (term.free_variable (depth A)))
| elimE {Γ Q}{A}(h1: proof Γ (∃ᵢ A))(h2: proof (Q ∪ {A}) B): proof (Γ ∪ Q) B
-- def substitution_term {σ : Signature} : term σ → Nat → term σ  → term σ -- substitution_term t x t' substitutes t' for x in t
-- | term.free_variable x, y, t => if x = y then t else term.free_variable x
-- | term.function_application f ts, y, t => term.function_application f (fun i => substitution_term (ts i) y t)

-- -- def substitution_formula {σ : Signature} : formula σ → Nat → term σ → formula σ := by
-- -- intro f x t
-- -- cases f with
-- -- | atomic_formula r ts => exact (formula.atomic_formula r (fun i=> substitution_term (ts i) x t))






-- instance{σ : Signature} (t : term σ) (y : Nat): Decidable (y ∈ free_variables_term t) := by match t with
-- | term.free_variable x => sorry
-- | term.function_application f ts => sorry


-- def decidable_free_variables_term {σ : Signature} (t : term σ) (y : Nat) : Decidable (y ∈ free_variables_term t):=
-- _
-- by cases t with
-- | free_variable x =>by constructor

-- | function_application f ts =>

-- def substitution_formula {σ : Signature} : formula σ → Nat → term σ → formula σ
-- | formula.bottom => fun _    => fun _ => ⊥
-- | formula.negation f=> fun x => fun t => substitution_formula f x t
-- | formula.atomic_formula r ts=> fun x => fun t => formula.atomic_formula r (fun i=> substitution_term (ts i) x t)
-- -- | formula.equalities t1 t2   => fun x => fun t => (substitution_term t1 x t) ≡ᵢ (substitution_term t2 x t)
-- | formula.implication f1 f2  => fun x => fun t => (substitution_formula f1 x t) →ᵢ (substitution_formula f2 x t)
-- | formula.conjunction f1 f2  => fun x => fun t => (substitution_formula f1 x t) ∧ᵢ (substitution_formula f2 x t)
-- | formula.disjunction f1 f2  => fun x => fun t => (substitution_formula f1 x t) ∨ᵢ (substitution_formula f2 x t)
-- | formula.existential_quantification y f => fun x => fun t =>if y ∈  free_variables_term t then formula.existential_quantification y f else formula.existential_quantification y (substitution_formula f x t)
-- | formula.universal_quantification y f => fun x => fun t => if y ∈  free_variables_term t then formula.universal_quantification y f else formula.universal_quantification y (substitution_formula f x t)
-- --solve it in the future


-- notation Γ "⊢" A => proof Γ A

-- def world := Nat


-- structure model (σ : Signature) :=
-- (W: Set world)
-- (R: world → world → Prop)
-- (supp: world → Set (formula σ) ) --How to specificate atomic formula
-- (refl : ∀ w ∈ W, R w w)
-- (trans : ∀ w ∈ W, ∀ v ∈ W, ∀ u ∈ W, R w v → R v u → R w u)
-- (mono : ∀ u ∈ W, ∀ v ∈ W, R u v → (supp u) ⊂ (supp v))



-- def force_form {σ : Signature}:  formula σ → world → (M: model σ ) →  Prop
-- | formula.atomic_formula r ts => fun w => fun M=> (formula.atomic_formula r ts) ∈ (M.supp w)
-- | formula.bottom => fun _ => fun _ => false
-- | formula.negation f => fun w => fun M=> ∀(v:world), M.R w v → ¬ (force_form f w M)
-- | formula.implication f1 f2 => fun w => fun M=> ∀ (v : world), M.R w v → force_form f1 v M → force_form f2 v M
-- | formula.conjunction f1 f2 => fun w => fun M=> (force_form f1 w M) ∧ (force_form f2 w M)
-- | formula.disjunction f1 f2 => fun w => fun M=> (force_form f1 w M) ∨ (force_form f2 w M)
-- | formula.existential_quantification x f => fun w => fun M=> ∃ (t: term σ ), force_form (substitution_formula f x t) w M
-- | formula.universal_quantification x f => fun w => fun M=> ∀ (t :term σ ),∀ (v:world), M.R w v → force_form (substitution_formula f x t) v M
-- -- | formula.equalities t1 t2 => fun w => sorry

-- def depth{σ : Signature}{f:formula σ}{M : model σ} {w:world}:  force_form f w M  → Nat


-- instance : partial_order force_form :=
-- {
--   le := leq,
--   le_refl := λ a, le_refl a,
--   le_trans := λ a b c, le_trans,
--   le_antisymm := λ a b, le_antisymm
-- }


-- def monoR {σ :Signature}{u v: world }{f:formula σ}{M : model σ}{z1:u ∈ M.W} {z2:v ∈ M.W}:M.R u v → force_form f u  M → force_form f v M := by
-- induction f
-- {
--   rename_i fr finr
--   intro hr hp
--   have dr:M.supp u ⊂ M.supp v
--   apply M.mono
--   assumption'}

















-- def semantic_consequence {σ : Signature} (Γ : Set (formula σ)) (A : formula σ) : Prop :=
-- ∀ (M : model σ), ∀ (w : world), (∀ (f :formula σ ),f ∈ Γ →  force_form f w M) → force_form A w M

-- notation Γ "⊧" A => semantic_consequence Γ A

-- lemma Zcombine {σ : Signature}{P Q: Set (formula σ)}{A B: formula σ} : (P ⊧ A) →  (Q ⊧ B ) → ((P ∪ Q) ⊧ (A ∧ᵢ B) ):=by
-- intro h1 h2
-- apply h1





----proof of soundness
-- def soundness {σ: Signature}{Q: Set (formula σ )}{A : formula σ } : (Q ⊢ A) → (Q ⊧ A) := by
-- intro h
-- cases h with
-- | ref hp => intro M w h1;apply h1;assumption
-- | introI A B hx =>
--   intro M w h1
--   have q:∀ (v : world), M.R w v → force_form A v M → force_form B v M:=by
--     intro v raa c1
--     have ss:(Q ∪ {A})⊧B:= (soundness hx)
--     apply ss
--     intro xf tx
--     cases tx with
--     | inl h0 =>
