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
| free_variable : ℤ  → term σ
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




def free_variables_term {σ : Signature} : term σ → ℤ  → Set ℤ
| term.free_variable x => fun bound => if x>= bound then {x} else ∅
| term.Constant _=> fun _ =>∅


def free_variables_formula {σ : Signature} : formula σ → ℤ  → Set ℤ
| formula.atomic_formula r ts=>fun bound=> ⋃ (i:Fin (σ.arity' r)),free_variables_term (ts i) bound
| formula.negation f => fun bound=> free_variables_formula f bound
| formula.bottom =>fun _ => ∅
| formula.conjunction f1 f2 => fun bound =>(free_variables_formula f1 bound).union (free_variables_formula f2 bound)
| formula.disjunction f1 f2 => fun bound =>(free_variables_formula f1 bound).union (free_variables_formula f2 bound)
| formula.implication f1 f2 => fun bound =>(free_variables_formula f1 bound).union (free_variables_formula f2 bound)
| formula.existential_quantification f =>fun bound => free_variables_formula f (bound+1)
| formula.universal_quantification f => fun bound => free_variables_formula f (bound+1)

def free_variables_set {σ : Signature} : Set (formula σ) → Set ℤ :=
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
| introF {Γ}{A}(h1:proof Γ A)(x:ℤ )(h2: x ∉ (free_variables_set Γ)): proof Γ (∀ᵢ (formula_subsitution A (term.free_variable x) (term.free_variable (depth A))))
| elimF {Γ}{A}(h:proof Γ (∀ᵢ A))(τ: term σ):proof Γ (formula_lift (-1) 0 (formula_subsitution f (term.free_variable 0) (term_lift 1 0 τ)))
| introE {Γ}{A}(t: term σ)(h: proof Γ A ): proof Γ (∃ᵢ formula_subsitution A t (term.free_variable (depth A)))
| elimE {Γ Q}{A}(h1: proof Γ (∃ᵢ A))(h2: proof (Q ∪ {A}) B): proof (Γ ∪ Q) B

notation Γ "⊢" A => proof Γ A





-- instance{σ : Signature} (t : term σ) (y : Nat): Decidable (y ∈ free_variables_term t) := by match t with
-- | term.free_variable x => sorry
-- | term.function_application f ts => sorry


-- def decidable_free_variables_term {σ : Signature} (t : term σ) (y : Nat) : Decidable (y ∈ free_variables_term t):=
-- _
-- by cases t with
-- | free_variable x =>by constructor

-- | function_application f ts =>





def world := Type
def obj := Type

def restrict_formula {σ : Signature} : (Nat → obj ) → obj → term σ → obj :=
fun beta => fun free_obj => fun t => by cases t with
| free_variable _ => exact free_obj
| Constant n => exact beta n

structure model (σ : Signature) :=
(W: Set world)
(R: world → world → Prop)
(D: world → Set obj ) -- Domain
(α: (w:world) → σ.relation_symbols → (Fin (σ.arity' r) → (D w) ) → Prop)
(β: (w:world) → Nat → (D w) ) --Nat is the index of Constant
(refl : ∀ w ∈ W, R w w)
(trans : ∀ w ∈ W, ∀ v ∈ W, ∀ u ∈ W, R w v → R v u → R w u)
(mono : ∀ u ∈ W, ∀ v ∈ W, R u v → (D u) ⊂ (D v))
(natural_transfer: (u v: world) → R u v → (D u) → (D v)) --transfer obj in Du to Dv
(mono_R: ∀ u ∈ W, ∀ v ∈ W, ∀ r:σ.relation_symbols , ∀ args: (Fin (σ.arity' r) → (D u)), (h: R u v) → (α u r args) →  (α v r (fun q:Fin (σ.arity' r) => (natural_transfer u v h (args q)) )))


def modify_value_function{σ : Signature} : (M:model σ) → (term σ → (M.D w)) → ℤ → (M.D w) → (term σ → (M.D w)) :=
fun M=> fun v=> fun id => fun item => fun t=> by cases t with
| free_variable z => if id = z then exact item else exact (v (term.free_variable z))
| Constant z => exact v (term.Constant z)

def formula_relation{σ : Signature}:formula σ → formula σ → Prop := fun f1 =>fun f2 => (depth f1) < (depth f2)

def force_form {σ : Signature}: formula σ → Nat → (w:world) → (M:model σ) → (term σ → (M.D w)) → Prop
| formula.atomic_formula r ts => fun n =>fun w => fun M=> fun v=> M.α w r (fun index=> (v (term_lift (-n) 0 (ts index))))
| formula.bottom =>  fun _  => fun _ => fun _ => fun _ => false
| formula.negation f =>fun n=> fun w => fun M=> fun v=> ∀(u:world), (h:M.R w u) → ¬ (force_form f n u M) (fun t=> M.natural_transfer w u h (v t))
| formula.implication f1 f2 =>fun n=>  fun w => fun M=>  fun v=>∀ (u : world), (h:M.R w u) → (force_form f1 n w M v) → (force_form f2 n u M (fun t=> M.natural_transfer w u h (v t)))
| formula.conjunction f1 f2 =>fun n=>  fun w => fun M=>  fun v=> (force_form f1 n w M v) ∧ (force_form f2 n w M v)
| formula.disjunction f1 f2 =>fun n=>  fun w => fun M=>  fun v=> (force_form f1 n w M v) ∨ (force_form f2 n w M v)
| formula.existential_quantification f =>fun n=>  fun w => fun M=>  fun v=> ∃ (t:M.D w) , force_form (formula_subsitution f (term.free_variable (depth f)) (term.free_variable (-n-1))) (n+1) w M (modify_value_function M v (-n-1) t)
| formula.universal_quantification f =>fun n=>  fun w => fun M=>  fun v=> ∀ (t:M.D w) , force_form (formula_subsitution f (term.free_variable (depth f)) (term.free_variable (-n-1))) (n+1) w M (modify_value_function M v (-n-1) t)
-- | formula.equalities t1 t2 => fun w => sorry
decreasing_by sorry  --fix in the future


def semantic_consequence {σ : Signature} (Γ : Set (formula σ)) (A : formula σ) : Prop :=
∀ (M : model σ), ∀ (w : world), ∀ (v : term σ → (M.D w)), (∀ (f :formula σ ),f ∈ Γ →  force_form f 0 w M v) → force_form A 0 w M v

notation Γ "⊧" A => semantic_consequence Γ A

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
