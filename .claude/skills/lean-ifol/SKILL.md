---
name: lean-ifol
description: Build, type-check, and interactively prove in this IFOL/CLM Lean 4 project. Use whenever working on any CLM/*.lean file, checking whether a proof compiles, inspecting a goal state, or searching for Mathlib lemmas. Covers the pinned Lean v4.0.0 toolchain, `lake build`, and the JSON REPL for goal-state feedback.
---

# Lean workflow for the IFOL / CLM project

Formalization of intuitionistic first-order logic (soundness, completeness,
Kripke semantics) in Lean 4 + Mathlib.

## Environment (already installed)

| Component | Value |
|---|---|
| Toolchain | `leanprover/lean4:v4.0.0` (pinned by `lean-toolchain`) |
| elan | `~/.elan/bin` — **not on PATH by default**, prepend it |
| Mathlib | pinned rev `1937612` (2023-09-17), in `lake-packages/mathlib` |
| Deps layout | old-style `lake-packages/` (not `.lake/packages/`) |
| REPL | `/home/chen_dongheng/others/repl` (commit `b10cd34`, repinned to v4.0.0) |
| Proxy | `export http_proxy=http://10.7.128.181:11454 https_proxy=$http_proxy` |

Every shell command needs:

```bash
export PATH="$HOME/.elan/bin:$PATH"
```

Network access (git, `lake exe cache get`) additionally needs the proxy exports.

**This is Lean 4.0.0 / Mathlib from September 2023 — three years old.** Do not
reach for modern Mathlib names, `omega`, `grind`, or post-2023 API. When unsure a
lemma exists, check it in the REPL with `#check` or grep
`lake-packages/mathlib/Mathlib/` rather than guessing from memory.

## Building

There is **no `CLM.lean` root file**, so bare `lake build` fails with
`no such file or directory: ./CLM.lean`. Build modules explicitly:

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake build CLM.completeness2 CLM.de_equations CLM.soundness CLM.z_translate
```

Those four are the leaves; they transitively cover all 13 modules. To check one
file, `lake build CLM.<module>`.

Import DAG (leaves last):

```
IFOL ─┬─ encodable ── encode_term ── encode_ts ── encode_formula
      ├─ general ── pigeon ── completeness ─┬─ completeness2  (+ bijection)
      │                                     └─ z_translate
      ├─ bijection
      ├─ soundness
      └─ de_equations
```

Restoring Mathlib `.olean`s after a clean (fast, uses the upstream cache):

```bash
export http_proxy=http://10.7.128.181:11454 https_proxy=$http_proxy PATH="$HOME/.elan/bin:$PATH"
lake exe cache get
```

## Interactive checking with the REPL

`./run-repl.sh` starts the REPL with `LEAN_PATH` already pointing at this
project's `build/lib` plus all of `lake-packages`. It reads JSON commands on
stdin (blank line ends each) and writes JSON on stdout.

Check a snippet against the project environment:

```bash
printf '{"cmd": "import CLM.completeness\\nopen IFOL\\nexample (n : Nat) : n + 0 = n := by simp", "env": null}\n\n' \
  | ./run-repl.sh
```

Response fields:
- `"sorries"` — each unfinished goal with its **full goal state** (`"goal"`) and position
- `"messages"` — errors, warnings, `#check`/`#eval` output, with line/column
- `"env"` — integer handle for the resulting environment

Reuse an environment to avoid re-importing Mathlib (which costs ~30–60s):

```bash
{ printf '{"cmd": "import CLM.completeness\\nopen IFOL", "env": null}\n\n'
  printf '{"cmd": "#check @Formula.force_form", "env": 0}\n\n'; } | ./run-repl.sh
```

**Use `sorry` deliberately to read goal states.** Replacing the rest of a proof
with `sorry` and reading the returned `"goal"` is the fastest way to see exactly
what remains — this substitutes for the interactive editor.

Note `import CLM.X` only works if `build/lib/CLM/X.olean` exists — build the
module first.

## Project conventions

- Everything lives in `namespace IFOL` (`CLM/IFOL.lean:6`) with `open Set`.
  Refer to `IFOL.Formula`, or `open IFOL` first.
- Notation: `⊢` for derivability, `∧ᵢ`/`∨ᵢ`/`→ᵢ`/`∃ᵢ`/`∀ᵢ` for the intuitionistic
  connectives. Defined in `CLM/IFOL.lean`.
- Terms use de Bruijn indices; `lift`/`down`/`Substitution` machinery is in
  `CLM/IFOL.lean`. This representation has been revised (see git history:
  `fix lift`, `NewBruijn`), which is what broke the downstream proofs below.

## SEMANTICS CHANGED 2026-07-27: expanding domains

The old constant-domain semantics made completeness FALSE (CD axiom valid but
underivable — see `/constant_domain_gap.lean`, now a historical non-compiling
record). `model` (CLM/IFOL.lean) now has `D : world → Set A` and
`D_mono : R u v → D u ⊆ D v`; `force_form`: `∃ᵢ f => ∃ t, t ∈ M.D w ∧ …`;
`∀ᵢ f => ∀ u, (h:M.R w u) → ∀ t, t ∈ M.D u → force at u (insert t)`;
`semantic_consequence` additionally requires `val_in M w v := ∀ t, v t ∈ M.D w`.
`soundness.lean` fully re-proved (val_in threaded through; `val_in_mono`).
`std Γ r` weakened to `is_inf Γ 0` only; `insertn`'s freshness pool now also
contains `{r}` (so Henkin witnesses avoid the goal by construction — needed
because the truth lemma's ∀-case goal contains one even constant).

## Completeness program status (2026-07-27, **FINISHED — sorry-free end to end**)

`completeness_final : (Γ ⊧ p) → (Γ ⊢ p)` (z_translate.lean) and `soundness`
both lake-build and depend only on [propext, Quot.sound, Classical.choice]
(REPL `#print axioms` audited; no sorryAx). Build the chain with
`lake build CLM.z_translate CLM.soundness`. `de_equations.lean` is dead
pre-existing scratch (syntax error + sorries, imported by nothing) — ignore;
there is no `CLM.lean` root, so package-level bare `lake build` fails by
design: always build per-module.

Design: canonical model with a language tower. Worlds = (prime consistent
theory, level k); `R (Δ,k) (Θ,l) = k ≤ l ∧ znF (l-k) '' Δ ⊆ Θ ∧ (Θ,l) ∈ worlds`;
domain elements A = ℕ×ℕ (birth level, ent-index), `D (Δ,k) = {a | a.1 ≤ k}`;
element (j,m) denotes at level k the term `tmc k (j,m) = znT (k-j) (det m)`;
valuation `valL k τ = (k, ent τ)`. Successor worlds z-translate (all constants
become odd) then `prime` (witnesses use fresh evens) — the odd/even recycling.
Truth lemma: `force (valL k) p at (Δ,k) ↔ Δ ⊢ p`.

| Module | Status |
|---|---|
| `rename.lean` (NEW) | **DONE, sorry-free.** Injective constant renaming `Term.rn/Formula.rn`, `consts`, `rename_proof`, `zc c = 2c+1`, `unz N` (explicit inverse-below-N injection), `z_provable_iff : (Γ⊢p) ↔ (rn zc '' Γ ⊢ rn zc p)`, `z_image_std`, `zc_consts_odd`, `rn_consts`, commutations rn/lift/down/Subst/inst/gen, FV transports. All inside `namespace IFOL` (Lean 4.0.0 needs this for dot notation). |
| `swap.lean` (NEW) | Free-variable swap `swf a b d` (d = binder depth; outer var x has index x+d), `swf_proof`, commutations (swf_inst_aux over Subst(free j)+down j with "e has no index ≤ j" hypothesis; swf_gen_aux), FV transports, `swf_id_of_not_mem`. **DONE, sorry-free.** |
| `cv.lean` (NEW) | `cv c x d` = capture-avoiding const c ↦ free x. `subst_cv` (finite contexts; per-case discipline: run IHs at super-fresh x', assemble, then `swf_proof` swap x↔x' — legal because x ∉ FV(Γ)∪FV(B) by hypothesis and x' by choice; `swf_cv` rewrites the swapped sequent). `const_gen : Γ ⊢ A.inst(const c) → c fresh → Γ ⊢ ∀ᵢA` via Finset_proof + fresh var + subst_cv + introF + `inst_gen_id`. **DONE, sorry-free** (agent-completed; axioms clean). |
| `completeness2.lean` | **COMPLETE modulo `const_gen`** (REPL-verified 0 errors with a sorried const_gen stub). Model fields, `force_tm_agree`, `force_shift` (general-u form), `bridge_univ`, `no_even_in_z_image/consts`, `tt_atomic/tt_bot`, full truth lemma `model_tt_iff_prf_aux` (all 6 cases incl. both level-(k+1) successor constructions), `completeness (hstd)`. `force_rn` lives in rename.lean. **DONE, lake-builds** (`import CLM.cv` re-enabled). |
| `z_translate.lean` | REWRITTEN & REPL-verified (0 errors on the stubbed chain): `z_semantic` (semantic transfer via force_rn with valuation v∘rn zc — no inverse map needed) + `completeness_final : (Γ ⊧ p) → (Γ ⊢ p)` unconditioned. |

Truth lemma case plan (sizes via rn_size; IH on formula size):
- →ᵢ force→prf: if ¬(Δ∪{f1} ⊢ f2), set Θ := prime (znF 1 '' (Δ∪{f1})) (znF 1 f2),
  u := (Θ, k+1). std by z_image_std; unprovability transported by z_provable_iff
  (znF 1 = rn zc via `znF_one_eq`). force f1 at u via force_shift + IH + ref;
  the assumed →ᵢ clause + shift + IH gives Θ ⊢ znF 1 f2, contra prime_no_prf.
- →ᵢ prf→force: zn_provable (rename_proof (zcn_inj m)) + subset from R + elimI.
- ∃ force→prf: witness t, τ := tmc k t; force_tm_agree to insert (valL k) (valL k τ);
  force_inst (soundness.lean); IH; introE.
- ∃ prf→force: has_const + provable_p_bot give Δ ⊢ f.inst (const c);
  t := valL k (const c); force_inst + IH.
- ∀ prf→force: at successor (Θ,l), τ := tmc l t; zn_provable + elimF τ + IH +
  force_inst + force_rn + force_tm_agree chain back to insert (valL k) t.
- ∀ force→prf: if ¬(Δ ⊢ ∀ᵢf): ¬(znF 1 '' Δ ⊢ ∀ᵢ(znF 1 f)) (z_provable_iff);
  const 0 is even hence fresh for the all-odd znF-image (zc_consts_odd), so by
  const_gen (contrapositive) ¬(znF 1 '' Δ ⊢ (znF 1 f).inst (const 0));
  Θ := prime (znF 1 '' Δ) ((znF 1 f).inst (const 0)), u := (Θ,k+1),
  t := valL (k+1) (const 0); the assumed ∀-clause at u,t + bridge chain + IH
  yields Θ ⊢ (znF 1 f).inst (const 0), contra prime_no_prf.

Import DAG additions: rename → (swap, cv, completeness2); cv → completeness2;
completeness2 imports completeness, bijection, soundness, rename, cv.

## Older repairs (2026-07-27, earlier)

`soundness.lean`, `completeness.lean`, `pigeon.lean` sorry-free (see git log).
`de_equations.lean` still a broken scratch file (parse error :149) — untouched.

**Quantifier rules were repaired on 2026-07-27** (the old system was provably
unsound — see the historical machine-checked refutation in `/counterexample.lean`,
which intentionally no longer compiles). Current state of `CLM/IFOL.lean`:
- `Formula.inst A τ := (A.Substitution (Term.free 0) (τ.lift 0)).down 0` —
  instantiate a quantifier body at τ (outer coordinates).
- `Formula.gen A x := (A.lift 0).Substitution (Term.free (x+1)) (Term.free 0)` —
  abstract free variable x into a new binder.
- Rules: `introF : Γ⊢A → free x ∉ FV Γ → Γ⊢∀ᵢA.gen x`; `elimF τ : Γ⊢∀ᵢA →
  Γ⊢A.inst τ`; `introE τ : Γ⊢A.inst τ → Γ⊢∃ᵢA`; `elimE : Γ⊢∃ᵢA →
  Δ∪{A.inst τ}⊢B → τ∉FV Δ → τ∉FV B → τ∉FV(∃ᵢA) → Γ∪Δ⊢B` (the last freshness
  condition is NEW).
- The old `force_lift`/`force_down`/`force_Substitution`/`iforce_Substitution`
  are kept only because `pigeon.lean`/`completeness.lean` still mention them;
  they are cutoff-broken — never use them in new proofs, use `inst`/`gen`.

**`CLM/soundness.lean` is fully proved** (no sorry). Its lemma toolkit is
reusable for the completeness rework: `force_inst` (forcing–instantiation),
`force_gen` (forcing–abstraction), `force_subst_free`, `force_lift_iff`,
`force_agree` (coincidence lemma), `mem_free_terms_lift`, and the valuation
combinators `insert_at`/`update_free`/`update_term`/`skip_val`.

`completeness.lean` now breaks at 3 sites (Finset_proof `introE`/`elimE` cases,
`insertn_prf` :539) and needs `has_const`/`insert_c` switched from
`force_Substitution/force_down` to `Formula.inst`. Known design gap: the Henkin
witness constant in `insertn`/`insertn_prf` is chosen fresh only w.r.t. the
context, not w.r.t. the decoded formula `∃ᵢf` itself — the new `elimE` freshness
condition `τ ∉ FV(∃ᵢf)` therefore needs `set_max` to also range over `f`.

When a `soundness.lean`-style arity error appears, get the ground truth from the
actual inductive rather than guessing:

```bash
printf '{"cmd": "import CLM.IFOL\\nopen IFOL\\n#print Proof\\n#print Formula", "env": null}\n\n' | ./run-repl.sh
```

`Proof` constructors (`CLM/IFOL.lean:186`): `ref, introI, elimI, introA, elimA1,
elimA2, introO1, introO2, elimO, botE, introF, elimF, introE, elimE`.

`Formula` constructors (`CLM/IFOL.lean:17`): `atomic_formula, conjunction,
disjunction, existential_quantification, universal_quantification, implication,
bottom`.
