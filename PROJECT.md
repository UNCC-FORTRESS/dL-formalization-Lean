# dL-lean — a Lean 4 formalization of differential dynamic logic (dL)

**Scope:** syntax and denotational semantics of single-program dL. Standalone foundation.

This repo is a single-program dL foundation. It knows nothing about biprograms,
relational modalities, forall-exists reasoning, certificates, or any relCertifier
application — those live in separate downstream repos that will import this one.
If you find yourself reaching for relational or forall-exists concepts, you are
out of scope; stop and flag it.

## Primary reference (authoritative)

The authoritative source for syntax and semantics is **Figure 2** of the
relCertifier paper appendix (syntax and semantics of hybrid programs and dL).
Match those definitions exactly. Where anything else disagrees with Fig 2, Fig 2 wins.

## Reference repositories (structural insight only — NOT for porting)

- **Coq-dL** — https://github.com/LS-Lab/Coq-dL — GPLv3, bit-rotted. Read for
  definition shape and lemma ordering only. Do NOT copy or transliterate.
- **Isabelle-dL** — https://github.com/LS-Lab/Isabelle-dL — AFP-backed, maintained.
  Prefer as structural reference where the two disagree.

Clean-room from the published math (Fig 2 + papers), never from GPL source.
Translate onto Mathlib idioms; do not port.

## License

Apache 2.0. No GPL-derived content.

## Milestone sequence

Small sessions. Report definitions for review before proving metatheorems.

- **M1 — Syntax.** Terms, hybrid programs, dL formulas as inductive types.
  States as `V → ℝ`. **[current]**
- **M2 — Semantics.** `⟦α⟧ : State → State → Prop` and `⟦ϕ⟧ : State → Prop`,
  following Fig 2. Hard case: ODE `{x'=θ}&ψ` — quantify over solutions
  `Φ : [0,r] → State`, `Φ 0 = ν`, `Φ r = ν'`, `Φ t ∈ ⟦ψ⟧` throughout `[0,r]`.
  Use Mathlib `HasDerivAt` / `IsIntegralCurveOn`. Derive `[α]ϕ`; `⟨α⟩ϕ = ¬[α]¬ϕ`.
- **M3 — Basic metatheory.** `[?ϕ]ψ ↔ (ϕ → ψ)`, `[α;β]ϕ ↔ [α][β]ϕ`,
  `[α∪β]ϕ ↔ [α]ϕ ∧ [β]ϕ`, `⟨α⟩ϕ ↔ ¬[α]¬ϕ`, plus one concrete ODE example.
- **M4 — Loop semantics.** `⟦α*⟧` as reflexive-transitive closure + loop induction.

**Proof calculus — exploratory, not required.** After semantics + basic metatheory,
optionally attempt dL proof rules / uniform substitution. Scope narrowly, report
before investing.

## Discipline (every milestone)

- Learning mode: scaffold and explain; user drives proofs; explain errors and
  suggest tactics rather than pasting solutions unless explicitly asked.
- **Done means:** `lake build` green AND `grep -rn sorry` clean AND `#print axioms`
  on each proved result showing only `propext` / `Classical.choice` / `Quot.sound`
  (no `sorryAx`). Green build alone is never "done."
- Report definitions before proving metatheorems. Faithfulness to Fig 2 is the gate.
- Own git repo, Apache 2.0, commit at each green milestone.

## Fig 2 grammar (reproduced for reference)

```
θ, δ ::= x | c | θ ⊕ δ
α, β ::= x := θ | x := * | {x' = θ} & ψ | ?ϕ | α;β | α ∪ β | α*
ϕ, ψ ::= ⊤ | θ ∼ δ | ¬ϕ | ϕ ∧ ψ | ∀x. ϕ | [α]ϕ
```
State: `ν : V → ℝ`. `⟨α⟩ϕ = ¬[α]¬ϕ`. Derived: `∨, →, ∃` as usual.
