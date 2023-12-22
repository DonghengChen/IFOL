import Mathlib.Init.Set
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic
open Set



structure Signature where
  -- function_symbols : Type
  relation_symbols : Type
  -- arity : function_symbols → Nat
  arity' : relation_symbols → Nat

inductive free_variable : Type
| free_variable : ℤ → free_variable

inductive Constant : Type
| Constant : Nat → Constant

inductive Term (σ : Signature): Type
| free : free_variable  → Term σ
-- | function_application (f : σ.function_symbols) : (Fin (σ.arity f) → Term σ ) → Term σ
| const : Constant → Term σ --constant is key word in Lean 4
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
  | .free n, .free m => n = m
  | .const n, .const m => n = m
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
  | .free n =>by  cases n with
    | free_variable n'=> if n' < c then
    exact free (free_variable.free_variable n')
    else
      exact free (free_variable.free_variable (n'+i))

  -- | function_application f ts => exact Term.function_application f (fun q:Fin (σ.arity f)=> Term_lift i c (ts q))
  | .const n => const n

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
  | .free n, .free n' =>
    match n,n' with
    | .free_variable n, .free_variable n' => if n=n' then e else src
  | const n, const n' =>
    match n,n' with
    | .Constant n, .Constant n' => if n=n' then e else src
  | free n, const _ =>  free n
  | const n, free _ => const n


def Formula.depth : Formula σ → Nat
  | ¬ᵢ f => depth f
  | ∃ᵢ f | ∀ᵢ f => (depth f) + 1
  | f1 ∧ᵢ f2 | f1 ∨ᵢ f2 | f1 →ᵢ f2 => max (depth f1) (depth f2)
  | _ => 0

-- @[simp]
-- def Formula.size : Formula σ → Nat
--   | atomic_formula .. | ⊥ => 0
--   | ¬ᵢ f | ∃ᵢ f | ∀ᵢ f => f.size + 1
--   | f1 ∧ᵢ f2 | f1 ∨ᵢ f2 | f1 →ᵢ f2 => f1.size + f2.size +1

def Formula.subsitution (f : Formula σ) (m e: Term σ) : Formula σ :=
  match m with
  | .const t => match f with
    | atomic_formula r ts => (# r) (fun q => (ts q).subsitution  (.const t) e)
    | f1 ∧ᵢ f2 => (f1.subsitution (.const t) e) ∧ᵢ (f2.subsitution (.const t) e)
    | f1 ∨ᵢ f2 => (f1.subsitution (.const t) e) ∨ᵢ (f2.subsitution (.const t) e)
    | f1 →ᵢ f2 => (f1.subsitution (.const t) e) →ᵢ (f2.subsitution (.const t) e)
    | ⊥  => ⊥
    | ¬ᵢ f  => ¬ᵢ (f.subsitution (.const t) e)
    | ∃ᵢ f  => ∃ᵢ (f.subsitution (.const t) e)
    | ∀ᵢ f => ∀ᵢ (f.subsitution (.const t) e)
  | .free t => match f with
    | atomic_formula r ts => (# r) (fun q => (ts q).subsitution (.free t) e)
    | ⊥  => ⊥
    | ¬ᵢ f  => ¬ᵢ (f.subsitution (.free t) e)
    | ∃ᵢ f  => ∃ᵢ (f.subsitution (.free t) e)
    | ∀ᵢ f => ∀ᵢ (f.subsitution (.free t) e)
    | f1 ∧ᵢ f2 => let (top:ℕ)  := (max (depth f1) (depth f2) )
                  match t with
                  | .free_variable a => (f1.subsitution (.free (free_variable.free_variable (a + (f1.depth) - top))) e) ∧ᵢ (f2.subsitution (.free  (free_variable.free_variable (a + (depth f2) - top))) e)
    | f1 ∨ᵢ f2 => let (top:ℕ)  := (max (depth f1) (depth f2) )
                  match t with
                  | .free_variable t =>
                  (f1.subsitution (.free (free_variable.free_variable ( t+ (f1.depth) - top))) e) ∨ᵢ (f2.subsitution (.free  (free_variable.free_variable (t+(depth f2) - top))) e)
    | f1 →ᵢ f2 => let (top:ℕ)  := (max (depth f1) (depth f2) )
                  match t with
                  | .free_variable t =>
                  (f1.subsitution (.free (free_variable.free_variable ( t+ (f1.depth) - top))) e)  →ᵢ (f2.subsitution (.free  (free_variable.free_variable (t+(depth f2) - top))) e)

-- @[simp]
-- theorem size_of_substit_eq_size {f : Formula σ} : ∀ m e, (f.subsitution m e).size = f.size := by
--   induction f <;> (intro m e;cases m) <;> first | rfl | simp; aesop


def β_reduction (f : Formula σ) (t : Term σ) : Formula σ :=
match f with
| .atomic_formula r ts => (# r) ts
| f1 ∧ᵢ f2 => f1 ∧ᵢ f2
| f1 ∨ᵢ f2 => f1 ∨ᵢ f2
| f1 →ᵢ f2 => f1 →ᵢ f2
| ⊥  => ⊥
| ¬ᵢ f => ¬ᵢ f
| ∃ᵢ f => (f.subsitution (Term.free (free_variable.free_variable 0)) (Term.lift 1 0 t)).lift (-1) 0
| ∀ᵢ f => (f.subsitution (Term.free (free_variable.free_variable 0)) (Term.lift 1 0 t)).lift (-1) 0

def Term.free_variables {σ : Signature} : Term σ → ℤ  → Set ℤ
| free x => fun bound => match x with
  | .free_variable z =>if z>= bound then {z} else ∅
| const _ => fun _ => ∅

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
| elimI (A B)(Γ Q): Proof Γ (A →ᵢ B) → Proof Q A → Proof (Γ ∪ Q) B
| introA (Γ Q) (A B): Proof Γ A → Proof Q B → Proof (Γ ∪ Q) (A ∧ᵢ B)
| elimA1  (A B)(Γ): Proof Γ (A ∧ᵢ B) → Proof Γ A
| elimA2  (A B)(Γ): Proof Γ (A ∧ᵢ B) → Proof Γ B
| introO1 (A B)(Γ): Proof Γ A → Proof Γ (A ∨ᵢ B)
| introO2 (A B)(Γ): Proof Γ B →  Proof Γ (A ∨ᵢ B)
| elimO   (A B C)(Γ Q G): Proof Γ (A ∨ᵢ B) → Proof (G ∪ {A}) C → Proof (Q ∪ {B}) C → Proof (Γ ∪ Q ∪ G) C
| introN  (A B)(Γ Q): Proof (Γ∪{A}) B → Proof (Q∪{A}) (¬ᵢB) → Proof (Γ ∪ Q) (¬ᵢA)
| ine     (A B)(Γ): Proof Γ A → Proof Γ (¬ᵢA) → Proof Γ B
| introF (A)(Γ)(x) : Proof Γ A → x ∉ (Γ.free_variables) → Proof Γ (∀ᵢ (Formula.subsitution A (.free (free_variable.free_variable x)) (.free (free_variable.free_variable A.depth))))
| elimF  (A)(Γ)(τ: Term σ) : Proof Γ (∀ᵢ A) → Proof Γ (Formula.lift (-1) 0 (Formula.subsitution f (.free (free_variable.free_variable 0)) (τ.lift 1 0)))
| introE (A)(Γ)(t: Term σ) : Proof Γ A → Proof Γ (∃ᵢ A.subsitution t (.free (free_variable.free_variable A.depth)))
| elimE (A B)(Γ)(τ: Term σ): Proof Γ (∃ᵢ A) → Proof (Q ∪ {A.subsitution (Term.free (free_variable.free_variable (A.depth))) τ }) B →((τ.free_variables 0) ∩ (A.free_variables (A.depth))=∅ ) → Proof (Γ ∪ Q) B --fix lift

notation Γ "⊢" A => Proof Γ A


structure model (σ : Signature) where
  world : Type
  W: Set world
  A : Type --Domain
  R: world → world → Prop
  D: world → Set A  -- Domain
  α: (w:world) → (r : σ.relation_symbols) → (Fin (σ.arity' r) → A) → Prop
  β:  Nat → Set A  --Nat is the index of Constant
  refl : ∀ w ∈ W, R w w
  trans : ∀ w ∈ W, ∀ v ∈ W, ∀ u ∈ W, R w v → R v u → R w u
  obj_inc : (u v:world) → (h1: u ∈ W) → (h2: v ∈ W) →  R u v → D u ⊆ D v -- D u →  D v
  mono: (u v:world) → (h1: u ∈ W) → (h2: v ∈ W) → (r: σ.relation_symbols) →
    (args : (Fin (σ.arity' r) → A)) → (h: R u v) → α u r args →  (α v r args)--(mono u v h1 h2 h) --(α v r (fun x => mono u v h1 h2 h (args x)))
  R_closed : (u v:world) →  R u v → (u ∈ W)  → (v ∈ W)

def codomain {σ : Signature}(M : model σ)(w : M.world)(args : ((Type u) → M.A)) : Prop := ∀ (x: Type u), (args x) ∈ (M.D w)

def modify_value_function (M : model σ) (v : Term σ → M.A) (item : M.A) : Term σ → M.A --head insert
| .free z => match z with
  | .free_variable n => if n<=1 then item else v (.free (.free_variable (n+1)))
| .const z => v (.const z)


-- def Formula.relation (f1 f2: Formula σ) : Prop := f1.depth < f2.depth

def Formula.force_form (M:model σ)(w : M.world) (hw: w ∈ M.W) (v : Term σ → M.A) : Formula σ  → Prop
| atomic_formula r ts => M.α w r (fun index=> v (ts index))
| ⊥ => False
| ¬ᵢ f => ∀ (u : M.world) , (h:M.R w u) → (f.force_form  M u (M.R_closed w u h hw) v) → False
| f1 →ᵢ f2 => ∀ u, (h:M.R w u) → (f1.force_form  M u (M.R_closed w u h hw) v) → (f2.force_form  M u (M.R_closed w u h hw) v)
| f1 ∧ᵢ f2 => (f1.force_form  M w hw v) ∧ (f2.force_form  M w hw v)
| f1 ∨ᵢ f2 => (f1.force_form  M w hw v) ∨ (f2.force_form  M w hw v)
| ∃ᵢ f => ∃ (t:M.A), f.force_form M w hw (modify_value_function M v t)
| ∀ᵢ f => ∀ (t:M.A), f.force_form M w hw (modify_value_function M v t)
-- | Formula.equalities t1 t2 => fun w => sorry
-- termination_by _ n w M v f => f.size

lemma strong_connected {σ : Signature}(M: model σ)(u v w:M.world)(h0: u ∈ M.W)(h1: M.R u v)(h2: M.R v w):M.R u w := by
have h4: v ∈ M.W :=by apply M.R_closed u v h1 h0
have h5: w ∈ M.W := by apply M.R_closed v w h2 h4
apply M.trans u h0 v h4 w h5 h1 h2



lemma Formula.mono_proof {σ : Signature}(M: model σ)(u v:M.world)(hr: M.R u v)(g: Formula σ)(hw: u ∈ M.W)(val:Term σ → M.A)(h1: g.force_form M u hw val ): g.force_form M v (M.R_closed u v hr hw) val:=
  match g with
  | atomic_formula r ts =>  M.mono u v hw (M.R_closed u v hr hw) r (fun q => val (ts q)) hr h1
  | bottom => ‹_›
  | conjunction f1 f2 => ⟨f1.mono_proof _ _ _ hr _ _ h1.left,f2.mono_proof _ _ _ hr _ _  h1.right⟩
  | disjunction f1 f2 => h1.elim (fun h5 => .inl <| f1.mono_proof _ _ _ hr _ _ h5) (fun h6 => .inr <| f2.mono_proof _ _ _ hr _ _ h6)
  | negation _ => fun w2 hw2 =>
    have h3: w2 ∈ M.W := M.R_closed v w2 hw2 (M.R_closed u v hr hw)
    have h4: v  ∈ M.W :=  M.R_closed u v hr hw
    h1 _ <| M.trans u hw v h4 w2 h3 hr hw2
  | implication _ _  => fun w2 hw2 =>
    have h6: _ :=  strong_connected M u v w2 hw hr hw2
    h1 w2 h6
  | existential_quantification f =>
    let ⟨t,ht⟩ := h1
    ⟨t,(Formula.mono_proof M u v hr f hw (modify_value_function M val t) ht)⟩
  | universal_quantification f => fun t =>
    Formula.mono_proof M u v hr f hw (modify_value_function M val t) (h1 t)




def semantic_consequence {σ : Signature} (Γ : Set (Formula σ)) (A : Formula σ) : Prop :=
∀ (M : model σ), ∀ (w : M.world), ∀ (v : Term σ → M.A)(hw), (∀ (f :Formula σ ),f ∈ Γ → f.force_form  M w hw v) → A.force_form  M w hw v

notation Γ "⊧" A => semantic_consequence Γ A

def soundness  (h : Q ⊢ A) : (Q ⊧ A) := by rename_i σ
                                           exact
match h with
| Proof.ref h => fun M w v hw hs=> (hs A) h
| Proof.introI A B Γ h1 =>
                          fun M w v hw hf=>
                          have hs:_ :=soundness h1
                          have hx: A ∈ Γ∪{A}:= by simp
                          fun u hu ha=>
                          have huw:_:=M.R_closed w u hu hw
                          (hs M u v huw)
                          fun x hx => by
                          cases hx with
                          | inr hx1=> have hAx: x=A := by apply hx1
                                      rw [hAx]
                                      assumption
                          | inl hx2=> have hfx:_ := hf x hx2
                                      exact Formula.mono_proof M w u hu x hw v hfx
| Proof.elimI  A B Q X hb hc =>fun M u v hw hf =>
                              have hbs: _ := soundness hb M u v hw
                              have hcs: _ := soundness hc M u v hw
                              have hfb:
                                       (∀ (f : Formula σ), f ∈ Q → Formula.force_form M u hw v f)
                                        := fun f hfq => hf f (Set.mem_union_left _ hfq)
                              have hfc:
                                       (∀ (f : Formula σ), f ∈ X → Formula.force_form M u hw v f)
                                        := fun f hfx => hf f (Set.mem_union_right _ hfx)
                              have h1: Formula.force_form M u hw v A := hcs hfc
                              have h2: Formula.force_form M u hw v (A →ᵢ B) := hbs hfb
                              h2 u (M.refl u hw) h1

| Proof.introA Γ Q A B h1 h2 => fun M u v hw hf =>
                                have hbs: _ := soundness h1 M u v hw
                                have hcs: _ := soundness h2 M u v hw
                                have hfb:
                                         (∀ (f : Formula σ), f ∈ Γ → Formula.force_form M u hw v f)
                                          := fun f hfq => hf f (Set.mem_union_left _ hfq)
                                have hfc:
                                         (∀ (f : Formula σ), f ∈ Q → Formula.force_form M u hw v f)
                                          := fun f hfx => hf f (Set.mem_union_right _ hfx)
                                have h1: Formula.force_form M u hw v A := hbs hfb
                                have h2: Formula.force_form M u hw v B := hcs hfc
                                ⟨h1,h2⟩
| Proof.elimA1 A B Γ h1 => fun M u v hw hf =>((soundness h1 M u v hw) hf ).left
| Proof.elimA2 A B Γ h1 => fun M u v hw hf => ((soundness h1 M u v hw) hf ).right
| Proof.introO1 A B Γ h1 => fun M u v hw hf => Or.inl ((soundness h1 M u v hw) hf)
| Proof.introO2 A B Γ h1 => fun M u v hw hf => Or.inr ((soundness h1 M u v hw) hf)
| Proof.elimO A B C Γ Q G h1 h2 h3 => fun M u v hw hf =>
                                have hbs: _ := soundness h1 M u v hw
                                have hcs: _ := soundness h2 M u v hw
                                have hds: _ := soundness h3 M u v hw
                                have hfb: _ := hbs fun f hfq => hf f (Set.mem_union_left _ (Set.mem_union_left _ hfq))
                                have hfc:
                                         (∀ (f : Formula σ), f ∈ Q → Formula.force_form M u hw v f)
                                          := fun f hfx => hf f (Set.mem_union_left _ ((Set.mem_union_right _ hfx)))
                                have hfd:
                                         (∀ (f : Formula σ), f ∈ G → Formula.force_form M u hw v f)
                                          := fun f hfx => hf f (Set.mem_union_right _ hfx)
                                have hB:(Formula.force_form M u hw v B) → (∀ (f : Formula σ), f ∈ Q ∪ {B} → Formula.force_form M u hw v f) :=
                                         fun h4 f hx=> match hx with
                                                      | Or.inl hx1 => hfc f hx1
                                                      | Or.inr hx2 => have h5: f= B := by apply hx2
                                                                      by rw [h5];exact h4
                                have hA:(Formula.force_form M u hw v A) → (∀ (f : Formula σ), f ∈ G ∪ {A} → Formula.force_form M u hw v f) :=
                                         fun h4 f hx=> match hx with
                                                      | Or.inl hx1 => hfd f hx1
                                                      | Or.inr hx2 => have h5: f= A := by apply hx2
                                                                      by rw [h5];exact h4
                                Or.elim hfb (fun z=> hcs (hA z)) (fun z=> hds (hB z))

| Proof.introN A B Γ Q h1 h2 => fun M u v hu hf =>
                                fun w hw1 hw2 =>
                                have hw := M.R_closed u w hw1 hu
                                let hs1:= soundness h1 M w v hw
                                let hs2:= soundness h2 M w v hw
                                have hG:(Formula.force_form M w hw v A) →
                                (∀ (f : Formula σ), f ∈ Γ  ∪ {A} → Formula.force_form M w hw v f) :=
                                fun h4 f hx=> match hx with
                                                      | Or.inl hx1 => Formula.mono_proof M u w hw1 f hu v (hf f (Set.mem_union_left Q hx1))
                                                      | Or.inr hx2 => have h5: f= A := by apply hx2
                                                                      by rw [h5];exact h4
                                have hQ:(Formula.force_form M w hw v A) →
                                (∀ (f : Formula σ), f ∈ Q  ∪ {A} → Formula.force_form M w hw v f) :=
                                fun h4 f hx=> match hx with
                                                      | Or.inl hx1 => Formula.mono_proof M u w hw1 f hu v (hf f (Set.mem_union_right _ hx1))
                                                      | Or.inr hx2 => have h5: f= A := by apply hx2
                                                                      by rw [h5];exact h4
                                let ha1:=hs1 (hG hw2)
                                let ha2:=hs2 (hQ hw2)
                                by apply ha2 w (M.refl w hw) ha1 ;


                                -- have hB:Formula.force_form M w hw v B :=
| Proof.ine A B Γ h1 h2 => fun M u v hw hf =>
                                have hbs: _ := soundness h1 M u v hw hf
                                have hcs: _ := soundness h2 M u v hw hf
                                False.elim (hcs u (M.refl u hw) hbs)


| Proof.introF A Γ x h1 h2 => fun M u v hw hf => fun t ht => (h1 M u v hw (fun f hfq => hf f (Set.mem_union_left _ hfq))) (h2 M u v hw (fun f hfq => hf f (Set.mem_union_right _ hfq))) t ht
| Proof.elimF A Γ τ h1 => fun M u v hw hf => (h1 M u v hw (fun f hfq => hf f (Set.mem_union_left _ hfq))) (h1 M u v hw (fun f hfq => hf f (Set.mem_union_right _ hfq))) τ
| Proof.introE A Γ t h1 => fun M u v hw hf => Exists.intro (h1 M u v hw (fun f hfq => hf f (Set.mem_union_left _ hfq))) (h1 M u v hw (fun f hfq => hf f (Set.mem_union_right _ hfq)))
| Proof.elimE A B Γ τ h1 h2 h3 => fun M u v hw hf => Exists.elim (h1 M u v hw (fun f hfq => hf f (Set.mem_union_left _ hfq))) (fun t ht => (h2 M u v hw (fun f hfq => hf f (Set.mem_union_right _ hfq))) (h3 M u v hw ht))
