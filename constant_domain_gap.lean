/- HISTORICAL RECORD — this file INTENTIONALLY no longer compiles.
   ================================================================

Before 2026-07-27 the semantics in `CLM/IFOL.lean` was *constant-domain*
Kripke semantics: `Formula.force_form` interpreted both quantifiers over the
single type `M.A`, the same at every world.  Under that semantics the
constant-domain axiom

    CD :  ∀x (φ(x) ∨ ψ)  →  (∀x φ(x)) ∨ ψ        (x not free in ψ)

was valid (the machine-checked proof `CD_valid` below used to compile), yet CD
is not derivable in pure intuitionistic first-order logic (Görnemann 1971).
Hence the completeness theorem `(Γ ⊧ p) → (Γ ⊢ p)` was FALSE as stated, and
the `sorry` in the ∀-case of `model_tt_iff_mem_p` could never be filled.

The semantics has since been changed to *expanding-domain* Kripke semantics:
`model` now carries `D : world → Set A` with `D_mono : R u v → D u ⊆ D v`;
`∃ᵢ` picks its witness in `D w`; `∀ᵢ` quantifies over all future worlds and
their domains; `semantic_consequence` requires the valuation to land in `D w`
(`val_in`).  Under the new semantics pure IFOL is sound (re-proved in
`CLM/soundness.lean`) and complete, and the proof `CD_valid` below correctly
FAILS: in its ∀-clause the antecedent only provides `φ(t) ∨ ψ` at *future*
worlds `u` and elements `t ∈ D u`, while deciding `ψ` at the current world is
no longer enough to build the disjunction — new elements may appear later.

Kept for reference only; do not add this file to the build.

import CLM.IFOL
open IFOL
open Classical

abbrev sig2 : Signature := ⟨fun _ => 1⟩

def phi : Formula sig2 := Formula.atomic_formula 0 (fun _ => Term.free 0)
def psi : Formula sig2 := Formula.atomic_formula 1 (fun _ => Term.const 1)

def CD : Formula sig2 := (∀ᵢ (phi ∨ᵢ psi)) →ᵢ ((∀ᵢ phi) ∨ᵢ psi)

theorem CD_valid : (∅ : Set (Formula sig2)) ⊧ CD := by
  intro M w v hw _
  intro u hR hall
  by_cases hq : M.α u 1 (fun _ => v (Term.const 1))
  · right
    exact hq
  · left
    intro t                    -- ← under expanding domains this intro pattern
    cases hall t with          --   no longer matches the ∀-clause; the proof
    | inl hp => exact hp       --   breaks here, as it must.
    | inr hq' => exact absurd hq' hq
-/
