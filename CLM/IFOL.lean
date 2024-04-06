import Mathlib.Init.Set
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

namespace IFOL
open Set

structure Signature where
  arity' : Nat → Nat

inductive Term (σ : Signature): Type
| free : ℕ  → Term σ
| const : ℕ → Term σ

inductive Formula (σ : Signature) : Type
  | atomic_formula : (r : ℕ ) → (Fin (σ.arity' r) → Term σ ) → Formula σ
  | conjunction : Formula σ → Formula σ → Formula σ
  | disjunction : Formula σ → Formula σ → Formula σ
  | existential_quantification : Formula σ → Formula σ
  | universal_quantification :  Formula σ → Formula σ
  | implication : Formula σ → Formula σ → Formula σ
  | bottom : Formula σ

notation  "¬ᵢ" a => Formula.implication a Formula.bottom
infixr:50 "→ᵢ" => Formula.implication
infixr:40 "∧ᵢ" => Formula.conjunction
infixr:30 "∨ᵢ" => Formula.disjunction
prefix:25 "∃ᵢ" => Formula.existential_quantification
prefix:24 "∀ᵢ" => Formula.universal_quantification
prefix:19 "#" => Formula.atomic_formula
notation "⊥" => Formula.bottom


def Term.lift (c : Nat) : Term σ → Term σ -- lift one position
  | .free n => if n < c then Term.free n
    else free (n+1)
  | .const n => const n

def Term.down (c : Nat) : Term σ → Term σ --down one position
  | .free n =>if n < c then free n
    else free (n-1)
  | .const n => const n

def Formula.lift (c : Nat) : Formula σ → Formula σ
  | atomic_formula r ts => atomic_formula r (fun q:Fin (σ.arity' r)=> (ts q).lift c)
  | f1 ∧ᵢ f2 =>  (f1.lift c) ∧ᵢ (f2.lift c)
  | f1 ∨ᵢ f2 =>  (f1.lift c) ∨ᵢ (f2.lift c)
  | f1 →ᵢ f2 =>  (f1.lift c) →ᵢ (f2.lift c)
  | ∃ᵢ f =>  ∃ᵢ (f.lift (c+1))
  | ∀ᵢ f => ∀ᵢ (f.lift (c+1))
  | ⊥ => ⊥

def Formula.down (c : Nat) : Formula σ → Formula σ
  | atomic_formula r ts => atomic_formula r (fun q:Fin (σ.arity' r)=> (ts q).down c)
  | f1 ∧ᵢ f2 =>  (f1.down c) ∧ᵢ (f2.down c)
  | f1 ∨ᵢ f2 =>  (f1.down c) ∨ᵢ (f2.down c)
  | f1 →ᵢ f2 =>  (f1.down c) →ᵢ (f2.down c)
  | ∃ᵢ f =>  ∃ᵢ (f.down (c+1))
  | ∀ᵢ f => ∀ᵢ (f.down (c+1))
  | ⊥ => ⊥

def Term.Substitution (src m e: Term σ) : Term σ :=
  match src,m with
  | .free n, .free n' =>if n=n' then e else src
  | const n, const n' =>if n=n' then e else src
  | src    , _ => src


@[simp]
def Formula.size : Formula σ → Nat
  | atomic_formula .. | ⊥ => 0
  | ∃ᵢ f | ∀ᵢ f => f.size + 1
  | f1 ∧ᵢ f2 | f1 ∨ᵢ f2 | f1 →ᵢ f2 => f1.size + f2.size +1


def Formula.Substitution (f : Formula σ) (m e: Term σ): Formula σ :=
  match m with
  | .const t => match f with
    | atomic_formula r ts => (# r) (fun q => (ts q).Substitution  (.const t) e)
    | f1 ∧ᵢ f2 => (f1.Substitution (.const t) e ) ∧ᵢ (f2.Substitution (.const t) e )
    | f1 ∨ᵢ f2 => (f1.Substitution (.const t) e ) ∨ᵢ (f2.Substitution (.const t) e )
    | f1 →ᵢ f2 => (f1.Substitution (.const t) e ) →ᵢ (f2.Substitution (.const t) e )
    | ∃ᵢ f  => ∃ᵢ (f.Substitution (.const t) e )
    | ∀ᵢ f => ∀ᵢ (f.Substitution (.const t) e )
    | ⊥ => ⊥
  | .free t => match f with
    | atomic_formula r ts => (# r) (fun q => (ts q).Substitution (.free t) e)
    | ∃ᵢ f  => ∃ᵢ (f.Substitution ((Term.free t).lift 0) e )
    | ∀ᵢ f => ∀ᵢ  (f.Substitution ((Term.free t).lift 0) e )
    | f1 ∧ᵢ f2 => (f1.Substitution  (.free t) e ) ∧ᵢ (f2.Substitution  (.free t) e )
    | f1 ∨ᵢ f2 => (f1.Substitution  (.free t) e ) ∨ᵢ (f2.Substitution  (.free t) e )
    | f1 →ᵢ f2 =>  (f1.Substitution  (.free t) e ) →ᵢ  (f2.Substitution  (.free t) e )
    | ⊥ => ⊥


@[simp]
theorem size_of_substit_eq_size {f : Formula σ} : ∀ m e, (f.Substitution m e).size = f.size := by
  induction f <;> (intro m e;cases m) <;> first | rfl | simp; aesop

@[simp]
theorem size_of_down_eq_size {f : Formula σ} : ∀ c, (f.down c).size = f.size := by
  induction f <;> (intro m;cases m) <;> first | rfl | simp; aesop

@[simp]
theorem size_of_lift_eq_size {f : Formula σ} : ∀ c, (f.lift c).size = f.size := by
  induction f <;> (intro m;cases m) <;> first | rfl | simp; aesop


def Term.free_terms {σ : Signature}(t: Term σ)(bound : Nat) : Set (Term σ) :=
match t with
| free z =>  if z>= bound then {Term.free (z-bound)} else ∅
| const z => {Term.const z}

def Formula.free_terms {σ : Signature}(f : Formula σ)(bound : Nat) : Set (Term σ) :=
match f with
  | atomic_formula r ts => ⋃ (i:Fin (σ.arity' r)), (ts i).free_terms bound
  | f1 ∧ᵢ f2 | f1 ∨ᵢ f2 | f1 →ᵢ f2 =>
     (f1.free_terms bound) ∪ (f2.free_terms bound)
  | ∃ᵢ f | ∀ᵢ f =>
     f.free_terms (bound+1)
  | ⊥ => ∅

def Set.free_terms (Γ : Set (Formula σ)) : Set (Term σ) :=
  ⋃ (f ∈ Γ), f.free_terms 0


inductive Proof : (Γ:Set (Formula σ)) → Formula σ → Prop
| ref        : (A ∈ Γ) → Proof Γ A
| introI {A B Γ} : Proof (Γ∪{A}) B → Proof Γ (A →ᵢ B)
| elimI {A B Γ Q}: Proof Γ (A →ᵢ B) → Proof Q A → Proof (Γ ∪ Q) B
| introA {A B Γ Q}: Proof Γ A → Proof Q B → Proof (Γ ∪ Q) (A ∧ᵢ B)
| elimA1  {A B Γ}: Proof Γ (A ∧ᵢ B) → Proof Γ A
| elimA2  {A B Γ}: Proof Γ (A ∧ᵢ B) → Proof Γ B
| introO1 {A Γ}(B): Proof Γ A → Proof Γ (A ∨ᵢ B)
| introO2 {B Γ}(A): Proof Γ B →  Proof Γ (A ∨ᵢ B)
| elimO   {A B C Γ Q G}: Proof Γ (A ∨ᵢ B) → Proof (G ∪ {A}) C → Proof (Q ∪ {B}) C → Proof (Γ ∪ Q ∪ G) C
| botE {Γ}(A): Proof Γ ⊥ → Proof Γ A
| introF {A: Formula σ}{Γ}{x} :
Proof Γ A → x ∉ (Set.free_terms Γ) → Proof Γ (∀ᵢ (A.lift 0).Substitution x (Term.free 0))
| elimF  {A: Formula σ}{Γ}(τ: Term σ) :
Proof Γ (∀ᵢ A) → Proof Γ ((A.Substitution (Term.free 0) τ).down 0)
| introE {A : Formula σ}{Γ}{t: Term σ}{v : ℕ} :
Proof Γ (A.Substitution (Term.free v) t)  → Proof Γ (∃ᵢ (A.lift 0).Substitution (Term.free v) (Term.free 0))
| elimE {A B: Formula σ}{Γ Q: Set (Formula σ)}{τ: Term σ}:
Proof Γ (∃ᵢ A) → Proof (Q∪{(A.Substitution (Term.free 0) τ).down 0}) B →
τ ∉ (Set.free_terms Q) → τ ∉ (Formula.free_terms B 0)  →  Proof (Γ∪Q) B

notation Γ "⊢" A => Proof Γ A




structure model (σ : Signature) where
  world : Type
  W: Set world
  A : Type --Domain
  R: world → world → Prop
  α: (w:world) → (r : Nat) → (Fin (σ.arity' r) → A) → Prop
  refl : ∀ w ∈ W, R w w
  trans : ∀ w ∈ W, ∀ v ∈ W, ∀ u ∈ W, R w v → R v u → R w u
  mono: (u v:world) → (h1: u ∈ W) → (h2: v ∈ W) → (r: Nat) →
    (args : (Fin (σ.arity' r) → A)) → (h: R u v) → α u r args →  (α v r args)--(mono u v h1 h2 h) --(α v r (fun x => mono u v h1 h2 h (args x)))
  R_closed : (u v:world) →  R u v → (u ∈ W)  → (v ∈ W)

def insert_value_function (M : model σ) (v : Term σ → M.A) (item : M.A) : Term σ → M.A --head insert from zero
| .free n => if n=0 then item else v (.free (n+1))
| .const z => v (.const z)

def Formula.force_form (M:model σ)(w : M.world) (hw: w ∈ M.W) (v : Term σ → M.A) : Formula σ  → Prop
| atomic_formula r ts => M.α w r (fun index=> v (ts index))
| f1 →ᵢ f2 => ∀ u, (h:M.R w u) → (f1.force_form  M u (M.R_closed w u h hw) v) → (f2.force_form  M u (M.R_closed w u h hw) v)
| f1 ∧ᵢ f2 => (f1.force_form  M w hw v) ∧ (f2.force_form  M w hw v)
| f1 ∨ᵢ f2 => (f1.force_form  M w hw v) ∨ (f2.force_form  M w hw v)
| ∃ᵢ f => ∃ (t:M.A), f.force_form M w hw (insert_value_function M v t)
| ∀ᵢ f => ∀ (t:M.A), f.force_form M w hw (insert_value_function M v t)
| ⊥ => False

lemma strong_connected {σ : Signature}(M: model σ)(u v w:M.world)(h0: u ∈ M.W)(h1: M.R u v)(h2: M.R v w):M.R u w := by
have h4: v ∈ M.W :=by apply M.R_closed u v h1 h0
have h5: w ∈ M.W := by apply M.R_closed v w h2 h4
apply M.trans u h0 v h4 w h5 h1 h2


lemma Formula.mono_proof {σ : Signature}(M: model σ)(u v:M.world)(hr: M.R u v)(g: Formula σ)(hw: u ∈ M.W)(val:Term σ → M.A)(h1: g.force_form M u hw val ): g.force_form M v (M.R_closed u v hr hw) val:=
  match g with
  | atomic_formula r ts =>  M.mono u v hw (M.R_closed u v hr hw) r (fun q => val (ts q)) hr h1
  | conjunction f1 f2 => ⟨f1.mono_proof _ _ _ hr _ _ h1.left,f2.mono_proof _ _ _ hr _ _  h1.right⟩
  | disjunction f1 f2 => h1.elim (fun h5 => .inl <| f1.mono_proof _ _ _ hr _ _ h5) (fun h6 => .inr <| f2.mono_proof _ _ _ hr _ _ h6)
  | implication _ _  => fun w2 hw2 =>
    have h6: _ :=  strong_connected M u v w2 hw hr hw2
    h1 w2 h6
  | existential_quantification f =>
    let ⟨t,ht⟩ := h1
    ⟨t,(Formula.mono_proof M u v hr f hw (insert_value_function M val t) ht)⟩
  | universal_quantification f => fun t =>
    Formula.mono_proof M u v hr f hw (insert_value_function M val t) (h1 t)

def semantic_consequence {σ : Signature} (Γ : Set (Formula σ)) (A : Formula σ) : Prop :=
∀ (M : model σ), ∀ (w : M.world), ∀ (v : Term σ → M.A)(hw), (∀ (f :Formula σ ),f ∈ Γ → f.force_form  M w hw v) → A.force_form  M w hw v

notation Γ "⊧" A => semantic_consequence Γ A

end IFOL
