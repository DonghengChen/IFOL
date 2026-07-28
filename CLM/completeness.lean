/- Removing the `std` hypothesis from completeness.

`canonical.completeness` (CLM/canonical_model.lean) proves `(Γ ⊧ p) → (Γ ⊢ p)`
under `std Γ p` — no even constants in Γ.  The z-translation `rn zc`
(constants `c ↦ 2c+1`) makes any theory satisfy `std`; it preserves semantic
consequence (`z_semantic`, using the general bridge `force_rn`: pre-composing
the valuation with the renaming) and reflects provability (`z_provable_iff`,
CLM/const_rename.lean).  Chaining the three gives unconditional completeness. -/

import CLM.canonical_model
open IFOL
open Set
open Classical

variable {σ : Signature}

/-- The z-translation preserves semantic consequence. -/
lemma z_semantic {Γ : Set (Formula σ)} {p : Formula σ} (h : Γ ⊧ p) :
    ((Formula.rn zc) '' Γ) ⊧ (Formula.rn zc p) := by
  intro M0 w v hw hval hsat
  rw [force_rn]
  apply h M0 w (fun t => v (Term.rn zc t)) hw
  · intro t
    exact hval _
  · intro f hf
    rw [← force_rn]
    exact hsat _ (Set.mem_image_of_mem _ hf)

/-- Completeness of intuitionistic first-order logic for expanding-domain
Kripke semantics — no side conditions. -/
theorem completeness_final {Γ : Set (Formula σ)} {p : Formula σ} :
    (Γ ⊧ p) → (Γ ⊢ p) := by
  intro h
  apply (z_provable_iff Γ p).mpr
  exact canonical.completeness (z_image_std Γ (Formula.rn zc p)) (z_semantic h)
