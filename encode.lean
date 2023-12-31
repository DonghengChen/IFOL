/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad
-/

import Mathlib.Logic.Encodable.Basic
import Mathlib.Logic.Equiv.List
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic

/-
`Wfin α ar` is the type of finitely branching trees with labels from α, where
a node labeled `a` has `ar a` children.
-/

inductive Wfin {α : Type u} (ar : α → Nat) : Type u
| mk : (a : α) → (f : Fin (ar a) → Wfin ar) → Wfin ar

namespace Wfin

variable {α : Type*} {ar : α → ℕ}

def depth : Wfin ar → ℕ
| ⟨_, f⟩ => Finset.sup Finset.univ (fun n=> depth (f n)) + 1

def not_depth_le_zero (t : Wfin ar) : ¬ t.depth ≤ 0 :=
by cases t;apply Nat.not_succ_le_zero

lemma depth_lt_depth_mk (a : α) (f : Fin (ar a) → Wfin ar) (i : Fin (ar a)) :
  depth (f i) < depth ⟨a, f⟩ := by
  apply Nat.lt_succ_of_le
  let t:=Finset.mem_univ i
  apply Finset.le_sup t

-- Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))

end Wfin

/-
Show `Wfin` types are encodable.
-/



@[reducible] private def Wfin' {α : Type*} (ar : α → ℕ) (n : ℕ) :=
{ t : Wfin ar // t.depth ≤ n}

variable {α : Type*} {ar : α → ℕ}

private def encodable_zero : Encodable (Wfin' ar 0) :=
let f    : Wfin' ar 0 → Empty := λ ⟨x, h⟩ => absurd h (Wfin.not_depth_le_zero _)
let finv : Empty → Wfin' ar 0 := by  intro x; cases x
have h:∀ x, finv (f x) = x := λ ⟨x, h⟩ => absurd h (Wfin.not_depth_le_zero _)
Encodable.ofLeftInverse f finv h

private def f (n : Nat) : Wfin' ar (n + 1) → Σ a : α, Fin (ar a) → Wfin' ar n
| ⟨t, h⟩ =>
  match t with
  | ⟨a, f⟩ =>
    let h₀ : ∀ i : Fin (ar a), Wfin.depth (f i) ≤ n :=
      λ i => Nat.le_of_lt_succ (lt_of_lt_of_le (Wfin.depth_lt_depth_mk a f i) h)
    ⟨a, λ i : Fin (ar a) => ⟨f i, h₀ i⟩⟩


private def finv (n : Nat) : (Σ a : α, Fin (ar a) → Wfin' ar n) → Wfin' ar (n + 1)
| ⟨a, f⟩ =>
  let f' := λ i : Fin (ar a)=>(f i).val
  have h : Wfin.depth ⟨a, f'⟩ ≤ n + 1:=Nat.add_le_add_right (Finset.sup_le (λ b _=> (f b).2)) 1
  ⟨⟨a, f'⟩, h⟩

variable [Encodable α]

private def encodable_succ (n : Nat) (_ : Encodable (Wfin' ar n)) : Encodable (Wfin' ar (n + 1)) :=by
apply Encodable.ofLeftInverse (f n) (finv n)
intro t
cases t with
| mk a b=> cases a with
        | mk a f => rfl


instance : Encodable (Wfin ar) := by
  have h' : ∀ n, Encodable (Wfin' ar n) := λ n => by
    induction n with
    | zero => exact encodable_zero
    | succ n ih => exact encodable_succ n ih
  let f : Wfin ar → Σ n, Wfin' ar n   := λ t => ⟨t.depth, ⟨t, le_refl _⟩⟩
  let finv : (Σ n, Wfin' ar n) → Wfin ar := λ p => p.2.1
  have : ∀ t, finv (f t) = t:= λ t => by rfl
  exact Encodable.ofLeftInverse f finv this



/-
Make it easier to construct funtions from a small `fin`.
-/


variable {α : Type*}

def mk_fn0 : Fin 0 → α
| ⟨_, h⟩ => absurd h (Nat.not_lt_zero _) -- there are no values of type `Fin 0`


def mk_fn1 (t : α) : Fin 1 → α
| ⟨0, _⟩   => t
| ⟨n+1, h⟩ => have h2: n+1>=1 := Nat.succ_le_succ (Nat.zero_le n)
             have h3 := lt_of_lt_of_le h h2
             by simp at h3

def mk_fn2 (s t : α) : Fin 2 → α
| ⟨0, _⟩   => s
| ⟨1, _⟩   => t
| ⟨n+2, h⟩ => by simp at h



attribute [simp] mk_fn0 mk_fn1 mk_fn2

namespace Form

inductive relation_symbols : Type
| relation : Nat → relation_symbols

structure Signature where
  -- function_symbols : Type
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
  | atomic_formula : (r : relation_symbols) → (Fin (σ.arity' r) → Term σ ) → Formula σ
  | conjunction : Formula σ → Formula σ → Formula σ
  | disjunction : Formula σ → Formula σ → Formula σ
  | existential_quantification : Formula σ → Formula σ
  | universal_quantification :  Formula σ → Formula σ
  | implication : Formula σ → Formula σ → Formula σ
  | bottom : Formula σ
  | negation : Formula σ → Formula σ




private def construct:= ℤ ⊕ ℕ ⊕ Fin 11 ⊕ ℕ


local notation "cfree" v => Sum.inl v
local notation "cconst" v => Sum.inr (Sum.inl v)
local notation "catom" => Sum.inr (Sum.inr (Sum.inl 1) )
local notation "cbot"    => Sum.inr (Sum.inr (Sum.inl 2))
local notation "cimpl"   => Sum.inr (Sum.inr (Sum.inl 3))
local notation "cand"    => Sum.inr (Sum.inr (Sum.inl 4))
local notation "cor"     => Sum.inr (Sum.inr (Sum.inl 5))
local notation "cexists" => Sum.inr (Sum.inr (Sum.inl 6))
local notation "cforall" => Sum.inr (Sum.inr (Sum.inl 7))
local notation "cneg"    => Sum.inr (Sum.inr (Sum.inl 8))
local notation "cpar"    =>Sum.inr (Sum.inr (Sum.inl 9))
local notation "cend"    =>Sum.inr (Sum.inr (Sum.inl 0))
local notation "crel" n   =>Sum.inr (Sum.inr (Sum.inr n))
local notation "czero"  => Sum.inr (Sum.inr (Sum.inl 10))

@[reducible]
private def arity: construct → Nat
| (cfree _) => 0
| (cconst _)  => 0
| cbot      => 0
| cimpl     => 2
| cand      => 2
| cor       => 2
| cexists   => 1
| cforall   => 1
| cneg      => 1
| catom     => 2
| cpar      =>2
| (crel _)  =>0
| cend =>1
| czero =>0





def g{σ : Signature}: Form.Term σ → Wfin arity:=
fun term => by
cases term with
| free n => let m:= match n with
                    | .free_variable v => v
            exact ⟨cfree m, mk_fn0⟩
| const n =>let m:= match n with
                    | .Constant v => v
            exact ⟨cconst m, mk_fn0⟩

def gr: relation_symbols → Wfin arity:=
fun r => by
cases r with
| relation n => exact ⟨crel n,mk_fn0⟩







-- Restricting f to Fin (n - 1)

theorem foo (x :Fin (n-1)): x.val<n:=by
apply Nat.lt_of_lt_of_le x.2
norm_num






def s0: Fin 1 := ⟨0, by simp⟩
def s00: Fin 2 := ⟨0, by simp⟩
def s01: Fin 2 := ⟨1, by simp⟩

def p00:Nat.le 1 1:=by simp
def p01:Nat.le 1 2:=by simp
def p02:Nat.le 2 2:=by simp




def nmpm : ∀ (m : Nat), ¬m = 0 → m > 0 :=
  fun m =>
  match m with
  | 0 => fun h => absurd rfl h
  | m + 1 => fun _ => Nat.zero_lt_succ m


def gpar{σ : Signature} (n:Nat): (Fin m → Form.Term σ) → Wfin arity:= fun ts =>
if hm:m=0 then ⟨czero,mk_fn0⟩ else
if hn:n>0 then
⟨cpar, mk_fn2 (gpar (n-1) ts) (g (ts (Fin.ofNat' n (nmpm m hm))))  ⟩
else
⟨cpar ,mk_fn2 (g (ts (Fin.ofNat' n (nmpm m hm)))) (g (ts (Fin.ofNat' n (nmpm m hm))))⟩

def f {σ : Signature}:  Form.Formula σ → Wfin arity:=
  fun form =>by
    cases form with
    | atomic_formula r ts => exact ⟨catom,mk_fn2 (gr r) (gpar (σ.arity' r) ts)⟩
    | conjunction f1 f2 => exact ⟨cand, mk_fn2 (f f1) (f f2)⟩
    | disjunction f1 f2 => exact ⟨cor, mk_fn2 (f f1) (f f2)⟩
    | implication f1 f2 => exact ⟨cimpl, mk_fn2 (f f1) (f f2)⟩
    | bottom => exact ⟨cbot,mk_fn0⟩
    | negation f1 => exact ⟨cneg,mk_fn1 (f f1)⟩
    | existential_quantification f1 => exact ⟨cexists,mk_fn1 (f f1)⟩
    | universal_quantification f1 => exact ⟨cforall,mk_fn1 (f f1)⟩




private def decode0(σ : Signature) :Wfin arity → Term σ
| ⟨cfree v, _⟩ => Term.free (free_variable.free_variable v)
| ⟨cconst c, _⟩ => Term.const (Constant.Constant c)
| _ => Term.free (free_variable.free_variable 0)



def empty(n:Nat):Fin n → Term σ:=fun _ => Term.free (free_variable.free_variable 0)

private def decode1(σ : Signature):Wfin arity → (Fin n → Term σ)
| ⟨cpar, fn⟩ => fun x=> if x.val = n-1 then (decode0 σ (fn ⟨1, by reduce; exact p02⟩)) else decode1 σ (fn ⟨0, by reduce;exact p01⟩) x
| _ => fun _=> Term.free (free_variable.free_variable 0)--empty

private def decode2:Wfin arity → relation_symbols
| ⟨crel n, _⟩ => relation_symbols.relation n
| _ => relation_symbols.relation 0

private def finv {σ : Signature}: Wfin arity →  Form.Formula σ
| ⟨catom, fn⟩ => Form.Formula.atomic_formula (decode2 (fn ⟨0, by reduce;exact p01⟩)) (decode1 σ (fn ⟨1, by reduce;exact p02⟩))
| ⟨cbot, _⟩    => Form.Formula.bottom
| ⟨cimpl, fn⟩   => Form.Formula.implication (finv (fn ⟨0, by reduce;exact p01⟩)) (finv (fn ⟨1, by reduce;exact p02⟩))
| ⟨cand, fn⟩   => Form.Formula.conjunction (finv (fn ⟨0, by reduce;exact p01⟩)) (finv (fn ⟨1, by reduce;exact p02⟩))
| ⟨cor, fn⟩   => Form.Formula.disjunction (finv (fn ⟨0, by reduce;exact p01⟩)) (finv (fn ⟨1, by reduce;exact p02⟩))
| ⟨cexists, fn⟩   => Form.Formula.existential_quantification (finv (fn ⟨0, by reduce;exact p00⟩))
| ⟨cforall, fn⟩   => Form.Formula.universal_quantification (finv (fn ⟨0, by reduce;exact p00⟩))
| ⟨cneg, fn⟩   => Form.Formula.negation (finv (fn ⟨0, by reduce;exact p00⟩))
| _ => Form.Formula.bottom


theorem iso0{σ : Signature}: ∀ t:Form.Term σ , decode0 σ (g t) = t:= by
intro term
cases term with
| free n=> unfold Form.decode0
           unfold g
           simp
| const n=> unfold Form.decode0
            unfold g
            simp

theorem iso1{σ : Signature}{n:Nat}: ∀ ts:(Fin n → Form.Term σ), decode1 σ (gpar (n-1) ts)=ts := by


cases n
intro ts
funext X
absurd X.2
simp
unfold Form.decode1
rename_i n
simp


rename_i he hs

cases em (n=0) with
| inl h1=>
  rw [h1]
  have h0:Nat.succ 0=1:=by simp
  rw [h0]
  intro ts
  funext x
  unfold gpar
  have hx:x.val=0:=by simp
  simp
  





| inr h1=>
  have h2:n>0:=Nat.pos_of_ne_zero h1
  intro ts
  funext x
  cases em (x.val=n) with
  | inl h =>
    unfold gpar

  | inr h => simp [h,hs]
























theorem iso {σ : Signature}: ∀ k : Form.Formula σ, finv (f k) = k := by
  intro g
  sorry





-- instance [encodable ℕ] : encodable form :=
--   haveI : encodable (constructors σ) :=_
--     by { unfold constructors, apply_instance },
--   exact encodable.of_left_inverse f finv (by { intro p, induction p; simp [f, finv, *] })
instance [Encodable ℕ] {σ : Signature}: Encodable (Form.Formula σ) := by
  have h: Encodable (construct) := by unfold construct; sorry
  apply Encodable.ofLeftInverse (f) (finv) iso
