/-
Copyright (c) 2026 dL-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: dL-lean contributors
-/
import Mathlib

/-!
# dL syntax (Milestone 1)

Single-program differential dynamic logic (dL), syntax only.

The grammar follows **Figure 2** of the relCertifier appendix (authoritative):

```
θ, δ ::= x | c | θ ⊕ δ
α, β ::= x := θ | x := * | {x' = θ} & ψ | ?ϕ | α;β | α ∪ β | α*
ϕ, ψ ::= ⊤ | θ ∼ δ | ¬ϕ | ϕ ∧ ψ | ∀x. ϕ | [α]ϕ
```

Everything is parametrised by a variable type `V`. States (Milestone 2) will be
`V → ℝ`; no state structure is needed yet for syntax.

Design choices flagged for review are marked `NOTE:`.
-/

namespace DL

/-- Arithmetic operators `⊕` for terms.

NOTE: Fig 2 writes a single binary node `θ ⊕ δ` where "⊕ denotes arithmetics"
without enumerating the operators. We reify `⊕` as a small tag inductive rather
than carry a raw `ℝ → ℝ → ℝ` (which would destroy decidable structure and make
the term type non-inspectable). Seeded with `add`/`sub`/`mul` — enough for the
polynomial dynamics the paper targets. Division is omitted (partial on ℝ);
easy to add later if needed. -/
inductive AOp where
  | add
  | sub
  | mul
  deriving DecidableEq, Repr

/-- Comparison operators `∼` for atomic formulas.

NOTE: Fig 2 writes `θ ∼ δ` where "∼ denotes comparisons", again unenumerated.
Reified as a tag inductive over the six standard order/equality relations. -/
inductive CompOp where
  | eq
  | ne
  | lt
  | le
  | gt
  | ge
  deriving DecidableEq, Repr

/-- Terms `θ, δ ::= x | c | θ ⊕ δ`. Standalone (does not mention programs or
formulas), so a plain (non-mutual) inductive. -/
inductive Term (V : Type*) where
  /-- variable `x` -/
  | var : V → Term V
  /-- real constant `c` -/
  | const : ℝ → Term V
  /-- arithmetic `θ ⊕ δ` -/
  | binop : AOp → Term V → Term V → Term V

/-! Hybrid programs and dL formulas are mutually recursive: programs contain
formulas (`?ϕ`, the ODE domain `ψ`) and formulas contain programs (`[α]ϕ`).
They must live in a shared universe `u`, hence the explicit `universe`. -/

universe u

mutual

/-- Hybrid programs
`α, β ::= x := θ | x := * | {x' = θ} & ψ | ?ϕ | α;β | α ∪ β | α*`. -/
inductive Program (V : Type u) where
  /-- deterministic assignment `x := θ` -/
  | assign : V → Term V → Program V
  /-- nondeterministic assignment `x := *` -/
  | assignAny : V → Program V
  /-- continuous evolution `{x' = θ} & ψ`.

  NOTE: Fig 2's core grammar is single-variable (`{x' = θ}`); the prose notes
  `x` "can be a vector". We take the single-variable form here — one bound
  variable `x`, one right-hand term `θ`, one evolution-domain formula `ψ`.
  ODE systems are deferred (extend to a list of `V × Term V` later if a
  downstream milestone needs them). -/
  | ode : V → Term V → Formula V → Program V
  /-- test `?ϕ` -/
  | test : Formula V → Program V
  /-- sequential composition `α;β` -/
  | seq : Program V → Program V → Program V
  /-- nondeterministic choice `α ∪ β` -/
  | choice : Program V → Program V → Program V
  /-- repetition `α*` -/
  | star : Program V → Program V

/-- dL formulas `ϕ, ψ ::= ⊤ | θ ∼ δ | ¬ϕ | ϕ ∧ ψ | ∀x. ϕ | [α]ϕ`.

NOTE: only Fig 2's primitives are constructors. Derived forms
(`⊥, ∨, →, ↔, ∃, ⟨α⟩`) are abbreviations to be defined in Milestone 2. -/
inductive Formula (V : Type u) where
  /-- truth `⊤` -/
  | tt : Formula V
  /-- comparison `θ ∼ δ` -/
  | cmp : CompOp → Term V → Term V → Formula V
  /-- negation `¬ϕ` -/
  | neg : Formula V → Formula V
  /-- conjunction `ϕ ∧ ψ` -/
  | and : Formula V → Formula V → Formula V
  /-- universal `∀x. ϕ` -/
  | all : V → Formula V → Formula V
  /-- box modality `[α]ϕ` -/
  | box : Program V → Formula V → Formula V

end

end DL
