# The Proof Route

This document explains the overall architecture of the formalization — the
route to soundness and, in much more detail, completeness — and the *reasons*
behind the non-standard structures that appear in the code: the odd/even
constant mapping, the language tower, the birth-level domain elements, and the
constant-generalization machinery.

The two headline theorems:

```lean
theorem soundness          : (Γ ⊢ p) → (Γ ⊧ p)   -- CLM/soundness.lean
theorem completeness_final : (Γ ⊧ p) → (Γ ⊢ p)   -- CLM/completeness.lean
```

Both are sorry-free; `#print axioms` reports only `propext`, `Quot.sound`,
`Classical.choice`.

---

## 1. Syntax: two sorts of "variables" (`CLM/IFOL.lean`)

```lean
inductive Term (σ : Signature)
| free  : ℕ → Term σ      -- de Bruijn-indexed variables
| const : ℕ → Term σ      -- constants (Henkin witnesses)
```

Bound and free variables share the single de Bruijn index space `free n`:
under a binder every outer index is shifted (`lift`), and instantiating a
binder shifts back (`down`). Substitution of a *variable* is therefore
delicate — it must track binder depth.

**Why a separate constant sort?** Constants are completely inert under all
binder machinery: `lift`, `down`, and variable substitution leave `const c`
untouched, and `const c` can never be captured by a quantifier. This makes
constants the perfect carrier for *Henkin witnesses*: the completeness proof
constantly plugs witnesses into formulas under binders, and with constants
this requires no capture-avoidance bookkeeping at all. The price is paid once,
at a single point: the canonical model eventually needs to *generalize over a
constant* (§7), which is not a primitive rule. Everything else becomes
simpler; this trade is the reason for the design.

On top of the term language: `Formula.inst A τ` (instantiate the outermost
binder with `τ`) and `Formula.gen A x` (abstract the free variable `x` into a
new outermost binder). The natural-deduction system `Γ ⊢ p` has the usual
rules; the quantifier rules are

- `introF` : from `Γ ⊢ A` with the **eigenvariable condition**
  `free x ∉ FV(Γ)` infer `Γ ⊢ ∀ᵢ (A.gen x)`;
- `elimF`  : from `Γ ⊢ ∀ᵢ A` infer `Γ ⊢ A.inst τ` for any term `τ`;
- `introE` : from `Γ ⊢ A.inst τ` infer `Γ ⊢ ∃ᵢ A`;
- `elimE`  : existential elimination with a fresh witness term.

Note that `introF` generalizes over *variables*, not constants — this
asymmetry is what §7 has to repair.

## 2. Semantics: expanding-domain Kripke models (`CLM/IFOL.lean`)

A model carries a preordered set of worlds `W`, a domain assignment
`D : world → Set A` that **grows along accessibility**
(`D_mono : R u v → D u ⊆ D v`), and a monotone atomic valuation. Forcing is
standard intuitionistic forcing; the quantifier clauses are the expanding-
domain ones:

```
w ⊩ ∃ᵢ f   iff  some t ∈ D w satisfies f at w
w ⊩ ∀ᵢ f   iff  for EVERY u with R w u and every t ∈ D u, f holds at u
```

Semantic consequence `Γ ⊧ A` quantifies over worlds *and* over admissible
valuations — `val_in M w v`, i.e. every term denotes an element of `D w`.

**Why not constant domains?** The first version of this project used a single
domain for all worlds. Under that semantics the *constant-domain axiom*

```
∀x (φ ∨ ψ) → (∀x φ) ∨ ψ     (x not free in ψ)
```

is valid, but it is **not derivable** in intuitionistic first-order logic —
we verified this gap with a machine-checked counterexample before the rework
(see git history: `counterexample.lean`, `constant_domain_gap.lean`).
Completeness for the pure proof system is therefore *mathematically
impossible* over constant domains; expanding domains are forced on us, not a
stylistic choice.

## 3. Soundness (`CLM/soundness.lean`)

Induction over derivations. Two points are worth recording:

- The admissibility predicate `val_in` must be threaded through every case
  and re-established at future worlds (`val_in_mono`, using `D_mono`); the
  `elimF` case instantiates the universal at `v τ`, which lies in `D w`
  precisely because the valuation is admissible.
- The `introF` case inserts a *new* domain element at an arbitrary future
  world; the eigenvariable condition guarantees the context's semantics does
  not depend on the variable being reinterpreted.

## 4. Prime theories and the Henkin construction (`CLM/henkin.lean`)

Completeness needs, for each unprovable sequent, a *prime theory*: a
consistent, deductively closed set with

- the **disjunction property** (`f1 ∨ᵢ f2 ∈ Γ` implies `f1 ∈ Γ` or `f2 ∈ Γ`), and
- the **existence property** (`∃ᵢ f ∈ Γ` implies some instance
  `f.inst (const c) ∈ Γ`).

`prime Γ r` builds one above `Γ` while keeping `r` unprovable, by the usual
stage-wise enumeration: formulas are `Encodable`, and stage `n` decodes code
`n`. A decoded disjunction gets the disjunct that keeps `r` unprovable; a
decoded existential gets a **witness constant** — chosen as
`2 * set_max (…)`, an *even* number strictly larger than every constant seen
so far in the construction, in the current stage's pool, *and in the goal
`r`* (the pool literally contains `{r}`; §6 explains why the goal must be
protected).

Two design points:

- **`p_bot_form` padding (`CLM/pigeon.lean`).** Stage `n` only ever looks at
  the single formula with code `n` — but witness constants must be chosen
  fresh *at the stage where the existential is processed*, and one fixed
  stage may be too early. The fix: `p_bot_form p n = p ∨ᵢ ⊥ ∨ᵢ … ∨ᵢ ⊥` gives
  every formula infinitely many provably-equivalent syntactic variants, hence
  infinitely many codes, hence the enumeration revisits (a variant of) every
  formula at arbitrarily late stages. The existence property is accordingly
  stated up to padding, and `provable_p_bot` strips the padding when the
  theory is used.

- **The `std` side condition.** `std Γ r` says `Γ` contains **no even
  constants at all** (`is_inf Γ 0`). Since witnesses are always even and
  always larger than everything relevant, `std` guarantees the infinite
  supply of fresh witnesses never collides with the base theory. Of course,
  an arbitrary theory is not `std` — removing this hypothesis is exactly what
  the constant mapping is for.

## 5. The problem: closure pollution, and the constant mapping

Here is the central obstruction that shaped the whole design.

The canonical model for an intuitionistic logic needs *many* worlds: to
refute an unforced `f1 →ᵢ f2` at a world `Δ` we must build a *successor*
prime theory containing `Δ ∪ {f1}`; to refute an unforced `∀ᵢ f` we must
build a successor containing a fresh-constant instance. Both constructions
need fresh witness constants **relative to `Δ`**.

But `Δ` is a prime theory, hence deductively *closed* — and a closed theory
mentions essentially **every** constant (e.g. it proves `p →ᵢ p` for every
formula `p`, and membership pollutes the free-term set with every constant of
every such `p`). After one Henkin construction, the constant pool ℕ is
exhausted: *no* constant is fresh for `Δ`. A second Henkin construction on
top of `Δ` is impossible as-is. This is what we call **closure pollution**,
and it is why textbook proofs say "extend the language with new constants
`c₀, c₁, …`" — they take a *fresh copy* of the constant pool at every step.

Formalizing an actual ω-tower of ever-growing signature types would make
terms, formulas, and derivations heterogeneous across levels — every lemma
would become a lemma *family* with coercions. Instead, this project keeps
**one fixed signature** and simulates the tower inside ℕ with the

**constant mapping** `zc c = 2c + 1` (`CLM/const_rename.lean`):

- `Formula.rn zc` renames every constant `c` to `2c+1`. The image of *any*
  theory contains only **odd** constants; all the **evens are freed** and can
  serve as the next round of Henkin witnesses. This is the odd/even
  recycling: applying `zc` is exactly "extend the language by a fresh copy of
  the constants", except the "fresh copy" is carved out of the same ℕ.
- `rename_proof` : derivability is preserved by *any injective* constant
  renaming (constants are inert, so a derivation renames cleanly — one more
  payoff of the two-sort term design).
- `z_image_std` : the `zc`-image of any theory satisfies `std`, so `prime`
  applies to it.
- `z_provable_iff : (Γ ⊢ p) ↔ (rn zc '' Γ ⊢ rn zc p)`. The forward direction
  is `rename_proof`. The backward direction needs an *inverse* renaming — but
  `zc` is not surjective, so no global inverse exists. The trick (`unz N`):
  a derivation only uses **finitely many** formulas (`Finset_proof`), so
  choose `N` above every constant occurring in it; `unz N` halves odd
  constants below `N` and shifts everything else above `N`. It is injective
  and inverts `zc` on everything the derivation touches, so `rename_proof`
  applied to `unz N` pulls the derivation back.

So the successor of a world with theory `Δ` is:
**z-translate `Δ` (all constants become odd), then `prime` it (witnesses are
fresh evens).** Iterating gives the tower — each level reuses the single
ℕ-indexed pool.

## 6. The canonical model: a language tower (`CLM/canonical_model.lean`)

Because theories at different "generations" are written in differently
translated vocabularies, a world must remember its generation. Worlds are
pairs:

```
world  =  (Δ, k)   —  Δ a consistent prime theory, k its level
R (Δ,k) (Θ,l)  ⟺  k ≤ l  ∧  znF (l−k) '' Δ ⊆ Θ   (znF n = n-fold zc-renaming)
```

Accessibility says: `Θ` extends `Δ` *as seen through `l−k` further rounds of
translation*. Reflexivity is `znF 0 = id`; transitivity is the additivity
`znF m ∘ znF n = znF (m+n)` of iterated renaming.

**Domain elements carry a birth certificate.** The same individual is denoted
by *different* terms at different levels (each level re-translates its
vocabulary), so a domain element cannot simply *be* a term. Instead:

```
A = ℕ × ℕ           -- (birth level j, code m of a term under ent/det)
D (Δ,k) = { a | a.1 ≤ k }             -- born at or before the current level
tmc k (j,m) = znT (k−j) (det m)       -- its denotation at level k ≥ j
```

`ent`/`det` (`CLM/term_bijection.lean`) is a bijection between terms and ℕ,
so "(term born at level j)" is a pair of numbers. The element `(j,m)` is
denoted at its birth level by the term `det m`, and at every later level `k`
by that term translated `k−j` more times — `tmc_shift` makes this coherent
along `R`. Two structural facts then come for free:

- `D_mono` is just `j ≤ k ≤ l` — domains **expand** along `R` because levels
  only grow. The semantics' expanding-domain shape is realized by birth
  levels, with genuinely *new* elements (`(k+1, ·)`) appearing at each
  successor. This is where the counterexample to constant-domain completeness
  is finally accommodated rather than contradicted.
- The canonical valuation at a world of level `k` is
  `valL k τ = (k, ent τ)`: every term denotes "itself, born now". It is
  trivially admissible (`val_in`), and `tmc k (valL k τ) = τ`.

The atomic valuation reads membership off the theory through `tmc`:
`α (Δ,k) r map ⟺ (all map i born by level k) ∧ atomic r (tmc k ∘ map) ∈ Δ`;
monotonicity of `α` along `R` is exactly `R`'s translation-image condition
applied to an atom.

Three *semantic bridge* lemmas mediate between forcing and provability:

- `force_tm_agree` — canonical forcing depends on a valuation only through
  the denoted terms `tmc k ∘ v`;
- `force_shift` — forcing `p` at a future world under the old valuation
  `valL k` equals forcing the translated `znF (l−k) p` under the native
  `valL l`;
- `bridge_univ` — forcing a quantifier body with an inserted element `t`
  equals forcing the (translated) instance at the term `tmc l t`.

## 7. The truth lemma, and why `const_gen` must exist

```
model_tt_iff_prf :  (Δ,k) ⊩ p  under valL k   ⟺   Δ ⊢ p
```

by strong induction on formula size. Atoms, `⊥`, `∧`, `∨` are direct (primality
gives the disjunction property). The two directions that *build successor
worlds* are:

**Implication, force → prove.** If `Δ ⊬ f1 →ᵢ f2` then `Δ ∪ {f1} ⊬ f2`, so
(after z-translation, which preserves this by `z_provable_iff`)
`Θ := prime (znF 1 '' (Δ ∪ {f1})) (znF 1 f2)` at level `k+1` is a world,
`R (Δ,k) (Θ,k+1)` holds, `Θ` forces `znF 1 f1` (it contains it), so by the
outer forcing and `force_shift` it forces `znF 1 f2` — but by the induction
hypothesis it would then *prove* `znF 1 f2`, which `prime` was built to avoid.

**Universal, force → prove.** Suppose `(Δ,k)` forces `∀ᵢ f` but `Δ ⊬ ∀ᵢ f`.
The key claim is

```
znF 1 '' Δ  ⊬  (znF 1 f).inst (const 0)
```

— for if it *did* prove this instance at the (even, hence completely fresh)
constant `0`, then generalizing over that constant would give
`znF 1 '' Δ ⊢ ∀ᵢ (znF 1 f) = znF 1 (∀ᵢ f)`, and `z_provable_iff` would pull
this back to `Δ ⊢ ∀ᵢ f`. Given the claim, build
`Θ := prime (znF 1 '' Δ) ((znF 1 f).inst (const 0))` at level `k+1`, take the
newborn element `t := (k+1, ent (const 0)) ∈ D Θ`; the outer forcing of
`∀ᵢ f` applies to `Θ` and `t`, and `bridge_univ` turns that into
`Θ ⊢ (znF 1 f).inst (const 0)` — contradiction with `prime`'s guarantee.

(This case is also why `insertn`'s freshness pool contains the goal `r`: here
the goal *itself* contains the even constant `0`, and the Henkin witnesses of
`Θ` must not collide with it.)

The step "generalizing over that constant" is the rule

```
const_gen :  Γ ⊢ A.inst (const c)  →  const c ∉ FV(Γ)  →  c ∉ consts(A)
             →  Γ ⊢ ∀ᵢ A                                (CLM/const_gen.lean)
```

which is **not** a primitive of the proof system — `introF` generalizes over
variables only. On paper one says "`c` was arbitrary, replace it by a fresh
variable throughout the derivation"; formally this is the most delicate piece
of the development, and it is why the modules `var_swap.lean` and
`const_gen.lean` exist:

- `subst_cv` proves that a derivation of `Γ ⊢ B` (with `Γ` **finite** — the
  reduction to finite contexts is `Finset_proof`) survives the substitution
  `const c ↦ free x`, provided `x` is fresh for `Γ` and `B`. The induction
  over the derivation has a classic quantifier-proof problem: internal cut
  formulas and **eigenvariables** of `introF`/`elimE` *inside* the derivation
  may collide with `x`, and nothing in the statement controls them.
- The resolution is the **swap discipline**: in each problematic case, run
  the induction hypotheses at a *super-fresh* variable `x′` (available
  because all contexts in sight are finite — `exists_fresh_var`), assemble
  the conclusion at `x′`, and finally apply the free-variable **swap**
  `x ↔ x′` to the whole sequent. A swap is a *bijective* renaming of free
  variables, so it maps derivations to derivations unconditionally
  (`swf_proof`, `CLM/var_swap.lean`) — unlike a one-directional substitution,
  it can never capture or merge anything. Since neither `x` (by hypothesis)
  nor `x′` (by choice) occurs in the final context or conclusion, the swap
  fixes both and simply retargets the substitution from `x′` to `x`.
- `const_gen` itself is then: shrink to a finite subcontext, pick a fresh
  `x`, apply `subst_cv` (the context is untouched since `c` does not occur in
  it; the conclusion becomes `A.inst (free x)`), apply the primitive `introF`,
  and rewrite `(A.inst (free x)).gen x = A` (`inst_gen_id`).

**Why not avoid constants and use variable witnesses throughout?** Then the
Henkin construction itself would need `introF`-style freshness for *free
variables* of an infinite closed theory — the same closure pollution appears
one level down, but now entangled with binder shifting (free variables are
not inert under `lift`/`down`). Constants keep the infinite combinatorics
clean and confine the difficulty to the single, finitary rule `const_gen`.

## 8. Final assembly (`CLM/completeness.lean`)

`canonical.completeness` gives `(Γ ⊧ p) → (Γ ⊢ p)` under `std Γ p`: if
`Γ ⊬ p`, the world `(prime Γ p, 0)` with valuation `valL 0` satisfies `Γ`
(truth lemma, right-to-left) but not `p` (truth lemma, left-to-right, plus
`prime`'s guarantee) — contradicting `Γ ⊧ p`.

The `std` hypothesis is removed by translating the *semantic* side as well:

- `z_semantic` : `Γ ⊧ p → (rn zc '' Γ) ⊧ (rn zc p)`. No inverse renaming is
  needed here — given a model and an admissible valuation `v`, pre-compose
  the valuation with the renaming (`force_rn`:
  `v ⊩ rn zc f  ↔  (v ∘ rn zc) ⊩ f`).
- Chain: `Γ ⊧ p` → (z_semantic) → `zc`-image `⊧` `zc`-image, which is `std`
  (`z_image_std`) → (canonical completeness) `zc`-image `⊢` `zc`-image →
  (`z_provable_iff`, backward, via `unz N`) → `Γ ⊢ p`. ∎

## 9. Summary: each special structure and its reason

| Structure | Why it exists |
|---|---|
| Constants as a separate term sort | Inert under all binder machinery — capture-free Henkin witnesses; injective renamings preserve derivations |
| Expanding domains `D`, `D_mono`, `val_in` | Constant domains validate the underivable CD axiom; completeness would be false |
| `p_bot_form` padding (`pigeon.lean`) | Gives every formula infinitely many codes, so the stage enumeration revisits existentials late enough for fresh witnesses |
| Even witnesses + `std` | Reserves a decidable half of the constant pool for witnesses; `std` = the base theory stays out of that half |
| Constant mapping `zc c = 2c+1` | Re-frees the even half after a Henkin closure ("extend the language" without changing the signature type) — defeats closure pollution |
| `unz N` | Finitary inverse of `zc`: pulls derivations back from the translated theory (`z_provable_iff` ←) |
| Worlds `(Δ, k)` with levels | Theories at different generations speak differently-translated vocabularies; `R` compares them through `znF (l−k)` |
| Domain `A = ℕ×ℕ` with birth levels, `tmc` | One individual is denoted by different terms at different levels; birth level makes `D_mono` literal and supplies genuinely new elements at successors |
| `ent`/`det` bijection | Lets domain elements *be* (level, term-code) pairs of numbers |
| Goal `r` in the witness-freshness pool | The ∀-case of the truth lemma primes against a goal that itself contains the even constant `0` |
| `const_gen` + `subst_cv` | The proof system generalizes over variables, the Henkin construction witnesses with constants; this admissible rule bridges the two |
| Variable swap `swf_proof` (`var_swap.lean`) | Bijective renaming is unconditionally derivation-preserving — resolves eigenvariable collisions in `subst_cv` via the "super-fresh `x′`, swap at the end" discipline |
