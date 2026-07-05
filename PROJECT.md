# dL-lean — a Lean 4 formalization of differential dynamic logic (dL)

**Scope:** syntax and denotational semantics of single-program dL, plus core
metatheory (loop induction, static semantics, differential invariants). Standalone
foundation.

This repo is a single-program dL foundation. It knows nothing about biprograms,
relational modalities, forall-exists reasoning, certificates, or any downstream
application — those live in separate repos that import this one. If you find
yourself reaching for relational or forall-exists concepts, you are out of scope.

## Grammar (standard single-program dL)

```
θ, δ ::= x | c | θ ⊕ δ
α, β ::= x := θ | x := * | {x' = θ} & ψ | ?ϕ | α;β | α ∪ β | α*
ϕ, ψ ::= ⊤ | θ ∼ δ | ¬ϕ | ϕ ∧ ψ | ∀x. ϕ | [α]ϕ
```
State: `ν : V → ℝ`. `⟨α⟩ϕ = ¬[α]¬ϕ`. Derived: `∨, →, ∃` as usual. ODEs are
vector-valued `{x⃗' = θ⃗} & ψ`; discrete assignments are single-variable.

## License

Apache 2.0.

## Milestones — all complete (see [STATUS.md](STATUS.md))

- **Syntax** — terms, hybrid programs, dL formulas as inductive types; states `V → ℝ`.
- **Semantics** — `⟦α⟧ : State → State → Prop` and `⟦ϕ⟧ : State → Prop`. ODE case:
  solutions `Φ : [0,r] → State` with simultaneous per-component `HasDerivWithinAt`
  (within `Icc 0 r`), masking of non-bound variables, and domain `ψ` throughout.
- **Basic metatheory** — `[?ϕ]ψ ↔ (ϕ→ψ)`, `[α;β]ϕ ↔ [α][β]ϕ`,
  `[α∪β]ϕ ↔ [α]ϕ ∧ [β]ϕ`, `⟨α⟩ϕ ↔ ¬[α]¬ϕ`, concrete ODE example.
- **ODE bridge** — per-component sem ↔ Mathlib `IsIntegralCurveOn` (unlocks
  Picard–Lindelöf / uniqueness / Grönwall via `[Fintype V]`).
- **Loop semantics** — `⟦α*⟧` as reflexive-transitive closure + loop induction.
- **Calculus core** — `K`, necessitation, monotonicity, semantic `[:=]`.
- **Static semantics** — `FV`/`BV`/`MBV`, frame-aware coincidence, bound-effect,
  `V` and `DW` consumers.
- **Differential invariants** — semantic Lie derivative; strict DI and domain-wide
  non-strict DI, with a counterexample delimiting the boundary-only check.

**Not built (deliberate):** sound boundary-only non-strict DI, differential ghosts,
uniform substitution, relational/biprogram layers. See [STATUS.md](STATUS.md).

## Reference implementations (structural insight only)

Two existing dL formalizations — `Coq-dL` and `Isabelle-dL` — were read for the
*shape* and ordering of definitions and lemmas (clean-room; nothing ported).
Everything here is stated and proved against this repo's own semantics.

## Discipline (every milestone)

- **Done means:** `lake build` green AND `grep -rn sorry` clean AND `#print axioms`
  on each proved result showing only `propext` / `Classical.choice` / `Quot.sound`
  (no `sorryAx`). A green build alone is never "done."
- Own git repo, Apache 2.0, commit at each green milestone.
