import CLM.completeness
open IFOL


-- def prime_has_disj {Γ :   Set (Formula σ)} {p q r : Formula σ} :
--   ((p ∨ᵢ q) ∈ prime Γ r) → p ∈ prime Γ r ∨ q ∈ prime Γ r :=by
--     intro h0
--     by_cases p ∈ prime Γ r
--     apply Or.inl ; assumption
--     apply Or.inr
--     apply prime_consq_iff_mem.mpr
--     have h1: ¬ (prime Γ r ⊢ p) := fun x => h (prime_consq_iff_mem.mpr x)
--     have h2:= prime_consq_iff_mem.mp h0
--     have l1:(prime Γ r ∪ {q})⊢q := by
--       apply Proof.ref
--       apply Set.mem_union_right
--       simp
--     have l2:(prime Γ r ∪ {p})⊢q := by

--     have h3:= Proof.elimO p q q (prime Γ r) (prime Γ r) (prime Γ r) h2 l2 l1
--     rw [Set.union_self] at h3
--     rw [Set.union_self] at h3
--     assumption
