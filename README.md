# IFOL — Intuitionistic First-Order Logic in Lean 4

A machine-checked formalization of intuitionistic first-order logic with
**soundness and completeness** for expanding-domain Kripke semantics.

```lean
theorem soundness          : (Γ ⊢ p) → (Γ ⊧ p)   -- CLM/soundness.lean
theorem completeness_final : (Γ ⊧ p) → (Γ ⊢ p)   -- CLM/completeness.lean
```

Both are sorry-free and depend only on the standard axioms
`propext`, `Quot.sound`, `Classical.choice`.

**[PROOF.md](PROOF.md)** documents the full proof route and the rationale for
the non-standard structures (the odd/even constant mapping, the language
tower, birth-level domain elements, constant generalization).

## Design

- **Syntax** (`CLM/IFOL.lean`): terms are de Bruijn indices (`free`) plus
  constants (`const`); a natural-deduction proof system `Γ ⊢ p`.
- **Semantics** (`CLM/IFOL.lean`): Kripke models with *monotonically expanding
  domains* `D : world → Set A` (`D_mono`). Valuations must land in the current
  world's domain (`val_in`). (Constant domains would validate the CD axiom
  `∀x(φ∨ψ) → (∀xφ)∨ψ`, which is not intuitionistically derivable, making
  completeness impossible; see git history for the machine-checked gap.)
- **Completeness**: a canonical model over a *language tower*. Worlds are pairs
  (prime consistent theory, level). To move one level up, the theory is
  translated by the constant renaming `c ↦ 2c+1` (all constants become odd) and
  then extended to a prime theory whose Henkin witnesses use fresh *even*
  constants — so every level reuses the single ℕ-indexed constant pool.
  The ∀-case of the truth lemma uses the admissible constant-generalization
  rule (`CLM/const_gen.lean`).

## Module map

| Module | Contents |
|---|---|
| `CLM/IFOL.lean` | Syntax, proof system, Kripke semantics (core definitions) |
| `CLM/proof_lemmas.lean` | Structural facts about `⊢` (weakening, substitution equations) |
| `CLM/encodable.lean`, `encode_term/ts/formula.lean` | Encodings (formula enumeration for the Henkin construction) |
| `CLM/term_bijection.lean` | The bijection `ent`/`det` between terms and ℕ |
| `CLM/pigeon.lean` | Freshness/pigeonhole lemmas for constants |
| `CLM/soundness.lean` | Soundness theorem |
| `CLM/henkin.lean` | Consistent-theory machinery: `insertn`, `prime`, primality and witness properties |
| `CLM/const_rename.lean` | Injective constant renaming; the z-translation `c ↦ 2c+1` and `z_provable_iff` |
| `CLM/var_swap.lean` | Free-variable swap and its action on derivations (`swf_proof`) |
| `CLM/const_gen.lean` | Constant→variable substitution `subst_cv`; the admissible rule `const_gen` |
| `CLM/canonical_model.lean` | The canonical model, truth lemma, completeness under `std` |
| `CLM/completeness.lean` | z-translation transfer; final unconditional `completeness_final` |

## Building

Requires the pinned toolchain `leanprover/lean4:v4.0.0` (see `lean-toolchain`);
Mathlib is fetched by lake (`lake exe cache get` to download prebuilt oleans).

```bash
lake build
```
