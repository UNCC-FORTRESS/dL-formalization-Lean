# dL-lean

A Lean 4 + Mathlib formalization of **differential dynamic logic (dL)**: syntax and
denotational semantics of single-program dL, following Figure 2 of the relCertifier
paper appendix.

Standalone foundation. No biprograms / relational modalities / certificates — those
belong to downstream repos that import this one. See [PROJECT.md](PROJECT.md) for
scope, milestones, and discipline.

## Status

- **M1 — Syntax** ✅ `DLLean/Syntax.lean` — terms, hybrid programs, dL formulas.
- M2 — Semantics — pending review of M1.

## Build

```sh
lake exe cache get   # prebuilt Mathlib oleans
lake build
```

Licensed under Apache 2.0.
