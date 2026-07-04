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

/-- A (vector) system of differential equations: an association of each evolving
variable `x` with the term `θ` giving its derivative `x' = θ`.

NOTE (choice 3, revised): Fig 2's prose says `x` "can be a vector of variables and
then θ is a vector of terms". A system `{x' = f(x,y), y' = g(x,y)}` is exactly a
list of `(x, f)`, `(y, g)`. Both reference formalizations use an isomorphic tree
(Isabelle `OSing`/`OProd`, Coq-dL `ODEsing`/`ODEprod`) and forbid a variable
appearing on two left-hand sides via a *separate* well-formedness predicate
(Isabelle `osafe`'s disjointness side-condition, Coq-dL `wf_ode`), not by the
datatype. We take the flat `List` (the tree's only extra generality was an
ODE-symbol constructor for uniform substitution, absent from Fig 2) and mirror the
"loose datatype + separate predicate" discipline via `ODESystem.WellFormed`.

Variables not named on any left-hand side stay constant during evolution (the M2
semantics holds them fixed; equivalently `y' = 0`), matching both refs. -/
abbrev ODESystem (V : Type*) := List (V × Term V)

/-- Well-formedness for a vector ODE: no variable is assigned a derivative twice
(each `x'` is defined at most once). Kept separate from the datatype, exactly as
Isabelle `osafe` / Coq-dL `wf_ode` do; consumed where the M2 semantics needs it. -/
def ODESystem.WellFormed {V : Type*} (sys : ODESystem V) : Prop :=
  (sys.map Prod.fst).Nodup

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
  /-- continuous evolution `{x' = θ} & ψ`, vector form: a system `sys` of
  equations `xᵢ' = θᵢ` evolving simultaneously, with evolution-domain formula `ψ`
  constraining the joint state throughout. Well-formedness (`sys.WellFormed`) is a
  separate predicate, not enforced here — see `ODESystem`. -/
  | ode : ODESystem V → Formula V → Program V
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
