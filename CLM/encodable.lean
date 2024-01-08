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

namespace encodable

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

namespace fin
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
