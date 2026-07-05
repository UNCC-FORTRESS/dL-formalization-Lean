# dL-lean

A Lean 4 + Mathlib formalization of **differential dynamic logic (dL)**: syntax,
denotational semantics, and core metatheory of single-program dL.

Standalone foundation. No biprograms / relational modalities / certificates — those
belong to downstream repos that import this one. See [PROJECT.md](PROJECT.md) for
scope and discipline, and [STATUS.md](STATUS.md) for the importable API.

## Status — foundation complete

All results: `lake build` green · `grep -rn sorry` clean · `#print axioms` =
`propext / Classical.choice / Quot.sound` only.

| Layer | File | Content |
|---|---|---|
| Syntax | [`Syntax.lean`](DLLean/Syntax.lean) | terms, hybrid programs, dL formulas; vector ODE `{x⃗'=θ⃗}&ψ` |
| Semantics | [`Semantics.lean`](DLLean/Semantics.lean) | `⟦α⟧`, `⟦ϕ⟧`; ODE = simultaneous derivs + masking + domain |
| Metatheory | [`Metatheory.lean`](DLLean/Metatheory.lean) | `[?]`,`[;]`,`[∪]`,`⟨·⟩` validities + a concrete ODE witness |
| ODE bridge | [`ODEBridge.lean`](DLLean/ODEBridge.lean) | per-component sem ↔ Mathlib `IsIntegralCurveOn` (existence / uniqueness / Grönwall) |
| Loop | [`Loop.lean`](DLLean/Loop.lean) | `⟦α*⟧` = `ReflTransGen`; loop induction + unfold |
| Calculus core | [`Calculus.lean`](DLLean/Calculus.lean) | `K`, necessitation, monotonicity, semantic `[:=]` |
| Static semantics | [`Static.lean`](DLLean/Static.lean) · [`Coincidence.lean`](DLLean/Coincidence.lean) | `FV`/`BV`/`MBV`; coincidence (frame-aware) + bound-effect; `V`, `DW` |
| Differential invariants | [`DI.lean`](DLLean/DI.lean) | semantic Lie derivative; strict + domain-wide non-strict DI |

## Build

```sh
lake exe cache get   # prebuilt Mathlib oleans
lake build
```

Licensed under Apache 2.0.
