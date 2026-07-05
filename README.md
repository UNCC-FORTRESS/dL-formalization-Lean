# dL-lean

A Lean 4 + Mathlib formalization of **differential dynamic logic (dL)**: syntax and
denotational semantics of single-program dL, following Figure 2 of the relCertifier
paper appendix.

Standalone foundation. No biprograms / relational modalities / certificates — those
belong to downstream repos that import this one. See [PROJECT.md](PROJECT.md) for
scope, milestones, and discipline.

## Status — foundation complete

All results: `lake build` green · `grep -rn sorry` clean · `#print axioms` =
`propext / Classical.choice / Quot.sound` only.

| Layer | File | Content |
|---|---|---|
| M1 Syntax | [`Syntax.lean`](DLLean/Syntax.lean) | terms, hybrid programs, dL formulas; vector ODE `{x⃗'=θ⃗}&ψ` |
| M2 Semantics | [`Semantics.lean`](DLLean/Semantics.lean) | `⟦α⟧`, `⟦ϕ⟧`; ODE = simultaneous derivs + masking + domain |
| M3 Metatheory | [`Metatheory.lean`](DLLean/Metatheory.lean) | `[?]`,`[;]`,`[∪]`,`⟨·⟩` validities + concrete ODE witness |
| ODE bridge | [`ODEBridge.lean`](DLLean/ODEBridge.lean) | per-component sem ↔ Mathlib `IsIntegralCurveOn` (PL / uniqueness / Grönwall) |
| M4 Loop | [`Loop.lean`](DLLean/Loop.lean) | `⟦α*⟧` = `ReflTransGen`; loop induction + unfold |
| Calculus (scout) | [`Calculus.lean`](DLLean/Calculus.lean) | `K`, necessitation, monotonicity, semantic `[:=]` |
| Static semantics | [`Static.lean`](DLLean/Static.lean) · [`Coincidence.lean`](DLLean/Coincidence.lean) | `FV`/`BV`/`MBV`; coincidence (frame-aware) + bound-effect; `V`, `DW` |

See [STATUS.md](STATUS.md) for the map downstream repos import against, and what is
deliberately **not** built (differential axioms, uniform substitution).

## Build

```sh
lake exe cache get   # prebuilt Mathlib oleans
lake build
```

Licensed under Apache 2.0.
