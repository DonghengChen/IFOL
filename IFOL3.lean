import Mathlib.Init.Set
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic
open Set



structure Signature where
  function_symbols : Type
  relation_symbols : Type
  arity : function_symbols → Nat
  arity' : relation_symbols → Nat

inductive Term (σ : Signature): Type
| free_variable : ℤ  → Term σ
-- | function_application (f : σ.function_symbols) : (Fin (σ.arity f) → Term σ ) → Term σ
| constant : Nat → Term σ --constant is key word in Lean 4
-- | relation_application (r : σ.relation_symbols) : (Fin (σ.arity' r) → Term σ )

inductive Formula (σ : Signature) : Type
  | atomic_formula : (r : σ.relation_symbols) → (Fin (σ.arity' r) → Term σ ) → Formula σ
  | conjunction : Formula σ → Formula σ → Formula σ
  | disjunction : Formula σ → Formula σ → Formula σ
  | existential_quantification : Formula σ → Formula σ
  | universal_quantification :  Formula σ → Formula σ
  | implication : Formula σ → Formula σ → Formula σ
  | bottom : Formula σ
  | negation : Formula σ → Formula σ

def Term_eql : Term σ → Term σ → Prop
  | .free_variable n, .free_variable m => n = m
  | .constant n, .constant m => n = m
  | _,_ => False


notation "⊥" => Formula.bottom
infixr:50 "→ᵢ" => Formula.implication
infixr:40 "∧ᵢ" => Formula.conjunction
infixr:30 "∨ᵢ" => Formula.disjunction
prefix:25 "∃ᵢ" => Formula.existential_quantification
prefix:24 "∀ᵢ" => Formula.universal_quantification
prefix:19 "#" => Formula.atomic_formula
prefix:20 "¬ᵢ" => Formula.negation


def Term.lift (i : ℤ) (c : Nat) : Term σ → Term σ --i c n → n
  | .free_variable n =>
    if n < c then
      free_variable n
    else
      free_variable (n+i)
  -- | function_application f ts => exact Term.function_application f (fun q:Fin (σ.arity f)=> Term_lift i c (ts q))
  | .constant n => constant n

def Formula.lift (i : ℤ) (c : Nat) : Formula σ → Formula σ
  | atomic_formula r ts => atomic_formula r (fun q:Fin (σ.arity' r)=> (ts q).lift i c)
  | f1 ∧ᵢ f2 =>  (f1.lift i c) ∧ᵢ (f2.lift i c)
  | f1 ∨ᵢ f2 =>  (f1.lift i c) ∨ᵢ (f2.lift i c)
  | f1 →ᵢ f2 =>  (f1.lift i c) →ᵢ (f2.lift i c)
  | ⊥ => ⊥
  | ¬ᵢ f =>  ¬ᵢ (f.lift i c)
  | ∃ᵢ f =>  ∃ᵢ (f.lift i (c+1))
  | ∀ᵢ f => ∀ᵢ (f.lift i (c+1))


def Term.subsitution (src m e: Term σ) : Term σ :=
  match src,m with
  | free_variable n, free_variable n' =>  if n=n' then e else free_variable n
  | constant n, constant n' => if n=n' then e else free_variable n
  | free_variable n, constant _ =>  free_variable n
  | constant n, free_variable _ => constant n


def Formula.depth : Formula σ → Nat
  | atomic_formula .. | ⊥ => 0
  | ¬ᵢ f => depth f
  | ∃ᵢ f | ∀ᵢ f => (depth f) + 1
  | f1 ∧ᵢ f2 | f1 ∨ᵢ f2 | f1 →ᵢ f2 => max (depth f1) (depth f2)

@[simp]
def Formula.size : Formula σ → Nat
  | atomic_formula .. | ⊥ => 0
  | ¬ᵢ f | ∃ᵢ f | ∀ᵢ f => f.size + 1
  | f1 ∧ᵢ f2 | f1 ∨ᵢ f2 | f1 →ᵢ f2 => f1.size + f2.size +1

def Formula.subsitution (f : Formula σ) (m e: Term σ) : Formula σ :=
  match m with
  | .constant t => match f with
    | atomic_formula r ts => (# r) (fun q => (ts q).subsitution  (.constant t) e)
    | f1 ∧ᵢ f2 => (f1.subsitution (.constant t) e) ∧ᵢ (f2.subsitution (.constant t) e)
    | f1 ∨ᵢ f2 => (f1.subsitution (.constant t) e) ∨ᵢ (f2.subsitution (.constant t) e)
    | f1 →ᵢ f2 => (f1.subsitution (.constant t) e) →ᵢ (f2.subsitution (.constant t) e)
    | ⊥  => ⊥
    | ¬ᵢ f  => ¬ᵢ (f.subsitution (.constant t) e)
    | ∃ᵢ f  => ∃ᵢ (f.subsitution (.constant t) e)
    | ∀ᵢ f => ∀ᵢ (f.subsitution (.constant t) e)
  | .free_variable t => match f with
    | atomic_formula r ts => (# r) (fun q => (ts q).subsitution (.free_variable t) e)
    | ⊥  => ⊥
    | ¬ᵢ f  => ¬ᵢ (f.subsitution (.free_variable t) e)
    | ∃ᵢ f  => ∃ᵢ (f.subsitution (.free_variable t) e)
    | ∀ᵢ f => ∀ᵢ (f.subsitution (.free_variable t) e)
    | f1 ∧ᵢ f2 => let (top:ℕ)  := (max (depth f1) (depth f2) )
                  (f1.subsitution (.free_variable (t+(depth f1) - top)) e) ∧ᵢ (f2.subsitution (.free_variable  (t+(depth f2) - top)) e)
    | f1 ∨ᵢ f2 => let (top:ℕ)  := (max (depth f1) (depth f2) )
                  (f1.subsitution (.free_variable (t+(depth f1) - top)) e) ∨ᵢ (f2.subsitution (.free_variable  (t+(depth f2) - top)) e)
    | f1 →ᵢ f2 => let (top:ℕ)  := (max (depth f1) (depth f2) )
                  (f1.subsitution (.free_variable (t+(depth f1) - top)) e)  →ᵢ (f2.subsitution (.free_variable  (t+(depth f2) - top)) e)

@[simp]
theorem size_of_substit_eq_size {f : Formula σ} : ∀ m e, (f.subsitution m e).size = f.size := by
  induction f <;> (intro m e;cases m) <;> first | rfl | simp; aesop


def β_reduction (f : Formula σ) (t : Term σ) : Formula σ :=
match f with
| .atomic_formula r ts => (# r) ts
| f1 ∧ᵢ f2 => f1 ∧ᵢ f2
| f1 ∨ᵢ f2 => f1 ∨ᵢ f2
| f1 →ᵢ f2 => f1 →ᵢ f2
| ⊥  => ⊥
| ¬ᵢ f => ¬ᵢ f
| ∃ᵢ f => (f.subsitution (Term.free_variable 0) (Term.lift 1 0 t)).lift (-1) 0
| ∀ᵢ f => (f.subsitution (Term.free_variable 0) (Term.lift 1 0 t)).lift (-1) 0

def Term.free_variables {σ : Signature} : Term σ → ℤ  → Set ℤ
| free_variable x => fun bound => if x>= bound then {x} else ∅
| constant _ => fun _ => ∅

def Formula.free_variables {σ : Signature} : Formula σ → ℤ  → Set ℤ
  | atomic_formula r ts => fun bound=> ⋃ (i:Fin (σ.arity' r)), (ts i).free_variables bound
  | ¬ᵢ f => fun bound => free_variables f bound
  | ⊥  => fun _ => ∅
  | f1 ∧ᵢ f2 | f1 ∨ᵢ f2 | f1 →ᵢ f2 =>
    fun bound => (f1.free_variables bound) ∪ (f2.free_variables bound)
  | ∃ᵢ f | ∀ᵢ f =>
    fun bound => f.free_variables (bound+1)

def Set.free_variables (Γ : Set (Formula σ)) : Set ℤ :=
  ⋃ (f ∈ Γ), f.free_variables 0


inductive Proof : (Γ:Set (Formula σ)) → Formula σ → Type
| ref        : (A ∈ Γ) → Proof Γ A
| introI (A B)(Γ) : Proof (Γ∪{A}) B → Proof Γ (A →ᵢ B)
| elimI : Proof Γ (A →ᵢ B) → Proof Q A → Proof (Γ ∪ Q) B
| introA  : Proof Γ A → Proof Q B → Proof (Γ ∪ Q) (A ∧ᵢ B)
| elimA1  : Proof Γ (A ∧ᵢ B) → Proof Γ A
| elimA2  : Proof Γ (A ∧ᵢ B) → Proof Γ B
| introO1 : Proof Γ A → Proof Γ (A ∨ᵢ B)
| introO2 : Proof Γ B →  Proof Γ (A ∨ᵢ B)
| elimO   : Proof Γ (A ∨ᵢ B) → Proof (Γ ∪ {A}) C → Proof (Γ ∪ {B}) C → Proof (Γ ∪ Q) C
| introN  : Proof (Γ∪{A}) B → Proof (Q∪{A}) (¬ᵢB) → Proof (Γ ∪ Q) (¬ᵢA)
| ine     : Proof Γ A → Proof Γ (¬ᵢA) → Proof Γ B
| introF (x) : Proof Γ A → x ∉ (Γ.free_variables) → x ∉ (Γ.free_variables) →
    Proof Γ (∀ᵢ (Formula.subsitution A (.free_variable x) (.free_variable A.depth)))
| elimF  (τ: Term σ) : Proof Γ (∀ᵢ A) → Proof Γ (Formula.lift (-1) 0 (Formula.subsitution f (.free_variable 0) (τ.lift 1 0)))
| introE (t: Term σ) : Proof Γ A → Proof Γ (∃ᵢ A.subsitution t (.free_variable A.depth))
| elimE : Proof Γ (∃ᵢ A) → Proof (Q ∪ {A}) B → Proof (Γ ∪ Q) B

notation Γ "⊢" A => Proof Γ A

-- instance{σ : Signature} (t : Term σ) (y : Nat): Decidable (y ∈ free_variables_Term t) := by match t with
-- | Term.free_variable x => sorry
-- | Term.function_application f ts => sorry


-- def decidable_free_variables_Term {σ : Signature} (t : Term σ) (y : Nat) : Decidable (y ∈ free_variables_Term t):=
-- _
-- by cases t with
-- | free_variable x =>by constructor

-- | function_application f ts =>



def restrict_formula {σ : Signature} : (Nat → obj ) → obj → Term σ → obj :=
fun beta => fun free_obj => fun t => by cases t with
| free_variable _ => exact free_obj
| constant n => exact beta n

-- def natural_transfer {σ : Signature} (M : model σ)(h1:u ∈ M.W)(h2:v∈ M.W)(h : M.R u v)(a: obj) :(a ∈ M.D u) → (a ∈ M.D v) :=
--   fun hu => M.mono u h1 v h2 h hu

-- variable (world : Type)
-- variable (  R: Nat → Nat → Prop)
-- variable (A : Type)
-- variable (σ : Signature) ( D: Nat → Set A )  ( W: Set Nat) (u v: Nat) (r : σ.relation_symbols) (world : Type)
-- (mono : (u v:Nat) → (h1: u ∈ W) → (h2: v ∈ W) →  R u v → ↑D u ⊆ ↑D v )

-- variable (args : (Fin (σ.arity' r) → D u))  (h1: u ∈ W) (h2: v ∈ W) (h: R u v) (x :  Fin (σ.arity' r))

-- --set_option pp.notation false

-- #check args x
-- #check mono u v h1 h2 h (args x)


structure model (σ : Signature) where
  world : Type
  W: Set world
  A : Type --Domain
  R: world → world → Prop
  D: world → Set A  -- Domain
  α: (w:world) → (r : σ.relation_symbols) → (Fin (σ.arity' r) → A) → Prop
  β: (w:world) → Nat → Set A  --Nat is the index of Constant
  refl : ∀ w ∈ W, R w w
  trans : ∀ w ∈ W, ∀ v ∈ W, ∀ u ∈ W, R w v → R v u → R w u
  obj_inc : (u v:world) → (h1: u ∈ W) → (h2: v ∈ W) →  R u v → D u ⊆ D v -- D u →  D v
  mono: (u v:world) → (h1: u ∈ W) → (h2: v ∈ W)→ (r: σ.relation_symbols) →
    (args : (Fin (σ.arity' r) → A)) → (h: R u v) → α u r args →  (α v r args)--(mono u v h1 h2 h) --(α v r (fun x => mono u v h1 h2 h (args x)))
  R_closed : (u v:world) →  R u v → (u ∈ W)  → (v ∈ W)

def codomain {σ : Signature}(M : model σ)(w : M.world)(args : ((Type u) → M.A)) : Prop := ∀ (x: Type u), (args x) ∈ (M.D w)

def modify_value_function (M : model σ) (v : Term σ → M.A) (id : ℤ) (item : M.A) : Term σ → M.A
| .free_variable z => if id = z then item else v (.free_variable z)
| .constant z => v (.constant z)


-- def Formula.relation (f1 f2: Formula σ) : Prop := f1.depth < f2.depth

def Formula.force_form (n: Nat)(M:model σ)(w : M.world) (hw: w ∈ M.W) (v : Term σ → M.A) : Formula σ  → Prop
| atomic_formula r ts => M.α w r (fun index=> (v (Term.lift (-n) 0 (ts index))))
| ⊥ => False
| ¬ᵢ f => ∀ (u : M.world) , (h:M.R w u) → ¬ (f.force_form n M u (M.R_closed w u h hw) v)
| f1 →ᵢ f2 => ∀ u, (h:M.R w u) → (f1.force_form n M u (M.R_closed w u h hw) v) → (f2.force_form n M u (M.R_closed w u h hw) v)
| f1 ∧ᵢ f2 => (f1.force_form n M w hw v) ∧ (f2.force_form n M w hw v)
| f1 ∨ᵢ f2 => (f1.force_form n M w hw v) ∨ (f2.force_form n M w hw v)
| ∃ᵢ f => ∃ (t:M.A), (f.subsitution (.free_variable f.depth) (.free_variable (-n-1))).force_form  (n+1) M w hw (modify_value_function M v (-n-1) t)
| ∀ᵢ f => ∀ (t:M.A), (f.subsitution (Term.free_variable (depth f)) (Term.free_variable (-n-1))).force_form (n+1) M w hw (modify_value_function M v (-n-1) t)
-- | Formula.equalities t1 t2 => fun w => sorry
termination_by _ n w M v f => f.size

lemma strong_connected {σ : Signature}(M: model σ)(u v w:M.world)(h0: u ∈ M.W)(h1: M.R u v)(h2: M.R v w):M.R u w := by
have h4: v ∈ M.W :=by apply M.R_closed u v h1 h0
have h5: w ∈ M.W := by apply M.R_closed v w h2 h4
apply M.trans u h0 v h4 w h5 h1 h2


lemma Formula.mono_proof {σ : Signature}(M: model σ)(u v:M.world)(hr: M.R u v)(f: Formula σ)(hw: u ∈ M.W)(val)(h1: f.force_form n M u hw val ): f.force_form n M v (M.R_closed u v hr hw) val:= by
  induction f with
  | atomic_formula r ts => unfold force_form at h1
                           unfold force_form
                           exact(M.mono u v hw (M.R_closed u v hr hw)  r (fun index=>  val (Term.lift (-n) 0 (ts index))) hr h1)
  | bottom => unfold force_form
              unfold force_form at h1
              assumption
  | conjunction f1 f2 => rename_i h3 h4
                         unfold force_form
                         apply And.intro
                         unfold force_form at h1
                         apply h3 h1.left
                         apply h4 h1.right
  | disjunction f1 f2 => rename_i h3 h4
                         unfold force_form
                         unfold force_form at h1
                         apply Or.elim h1
                         intro h5
                         apply Or.inl
                         apply h3 h5
                         intro h6
                         apply Or.inr
                         apply h4 h6
  | negation f => rename_i h0
                  unfold force_form
                  unfold force_form at h1
                  intro w2 hw2
                  apply h1
                  have h3: w2 ∈ M.W :=by apply M.R_closed v w2 hw2 (M.R_closed u v hr hw)
                  have h4: v ∈ M.W :=by apply M.R_closed u v hr hw
                  apply M.trans u hw v h4 w2 h3 hr hw2
  | implication f1 f2 f3 f4 => unfold force_form
                               unfold force_form at h1
                               intro w2 hw2
                               have h6: _ :=by apply strong_connected M u v w2 hw hr hw2
                               apply h1 w2 h6
  | existential_quantification f hv=>
                                unfold force_form
                                unfold force_form at h1
                                match h1 with
                                | ⟨t,ht⟩ =>  exact ⟨t,hv (modify_value_function M val t) ht⟩
  | universal_quantification f hv=>
                                unfold force_form
                                unfold force_form at h1
                                intro t
                                exact hv (modify_value_function M val t) (h1 t)

  -- | existential_quantification f h0=> unfold force_form
  --                                     unfold force_form at h1
  --                                     match h1 with
  --                                     | ⟨t,ht⟩ => exact ⟨t,(Formula.mono_proof M u v hr (subsitution f (Term.free_variable ↑(depth f)) (Term.free_variable (-↑n - 1))) hw (modify_value_function M val (-↑n - 1) t) ht)⟩
--   | universal_quantification f h0=> unfold force_form
--                                     unfold force_form at h1
--                                     intro t
--                                     have h2:_ :=h1 t
--                                     apply Formula.mono_proof M u v hr  (subsitution f (Term.free_variable ↑(depth f)) (Term.free_variable (-↑n - 1)))  hw (modify_value_function M val (-↑n - 1) t) h2
-- termination_by _ σ M u v h f hu val h1 => f.size
























                  -- apply M.R_closed







































def semantic_consequence {σ : Signature} (Γ : Set (Formula σ)) (A : Formula σ) : Prop :=
∀ (M : model σ), ∀ (w : M.world), ∀ (v : Term σ → M.A)(hw), (∀ (f :Formula σ ),f ∈ Γ → f.force_form 0 M w hw v) → A.force_form 0 M w hw v

notation Γ "⊧" A => semantic_consequence Γ A

-- lemma Zcombine {σ : Signature}{P Q: Set (formula σ)}{A B: Formula σ} : (P ⊧ A) →  (Q ⊧ B ) → ((P ∪ Q) ⊧ (A ∧ᵢ B) ):=by
-- intro h1 h2
-- apply h1





-- def soundness  (h : Q ⊢ A) : (Q ⊧ A) := by
-- induction h with
-- | ref hp D=>

-- | introI A B Γ h1 h2 => intro M w v h3
--                         unfold Formula.force_form
--                         intro u h4 h5



-- | introI A B Γ => intro M w v hf
--                   have hz:(Γ ∪ {A})⊧B := by assumption
--                   unfold Formula.force_form
--                   intro u h1 h2
