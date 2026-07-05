/-
Copyright (c) 2026 dL-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: dL-lean contributors
-/
import DLLean.Syntax

/-!
# dL denotational semantics (Milestone 2)

Following **Figure 2** of the relCertifier appendix.

* States are `State V := V → ℝ`.
* Term semantics `Term.eval : Term V → State V → ℝ` (Fig 2 `νJθK`).
* Program semantics `Program.sem : Program V → State V → State V → Prop`
  (Fig 2 `⟦α⟧`, the transition relation).
* Formula satisfaction `Formula.sat : Formula V → State V → Prop`
  (Fig 2 `⟦ϕ⟧`, the satisfying set as a predicate).

`Program.sem` and `Formula.sat` are mutually recursive (`[α]ϕ` needs `⟦α⟧`;
`?ϕ` and the ODE domain need `⟦ϕ⟧`). The box `[α]ϕ` is a `Formula.sat` case;
the diamond `⟨α⟩ϕ = ¬[α]¬ϕ` is a *derived* builder, not a constructor.

`NOTE:` marks a fidelity decision flagged for review.
-/

namespace DL

/-- A state assigns a real value to each variable (Fig 2: `ν : V → ℝ`). -/
abbrev State (V : Type*) := V → ℝ

/-- Interpretation of an arithmetic operator `⊕` as a real binary function
(Fig 2: `νJθ ⊕ δK = νJθK ⊕ νJδK`). -/
def AOp.interp : AOp → ℝ → ℝ → ℝ
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)

/-- Interpretation of a comparison operator `∼` as a real relation
(Fig 2: `νJθ ∼ δK` iff `νJθK ∼ νJδK`). -/
def CompOp.interp : CompOp → ℝ → ℝ → Prop
  | .eq => (· = ·)
  | .ne => (· ≠ ·)
  | .lt => (· < ·)
  | .le => (· ≤ ·)
  | .gt => (· > ·)
  | .ge => (· ≥ ·)

/-- Term semantics `νJθK` (Fig 2, term semantics block). -/
def Term.eval {V : Type*} : Term V → State V → ℝ
  | .var x,       ν => ν x
  | .const c,     _ => c
  | .binop op a b, ν => op.interp (a.eval ν) (b.eval ν)

/-- Left-hand-side (bound) variables of a vector ODE, as a `List V`.
`x` "is bound" means `x ∈ sys.bound`. Kept as a `List` (not `Finset`) so the
semantics needs no `DecidableEq V`; `x ∉ sys.bound` is a plain `Prop`.
Equal as a set to the review's `boundVars sys = (sys.map Prod.fst).toFinset`. -/
def ODESystem.bound {V : Type*} (sys : ODESystem V) : List V := sys.map Prod.fst

/-! ## Program transition relation `⟦α⟧` and formula satisfaction `⟦ϕ⟧`

Mutually recursive, structurally on the program/formula. -/

mutual

/-- Program semantics `⟦α⟧ : State → State → Prop` (Fig 2, program semantics).
`Program.sem α ν ν'` means "some execution of `α` goes from `ν` to `ν'`". -/
def Program.sem {V : Type*} : Program V → State V → State V → Prop
  -- `⟦x := θ⟧ = {(ν,ν') | ν'(x) = νJθK and ν'(y) = ν(y) for all y ≠ x}`.
  | .assign x θ, ν, ν' =>
      ν' x = θ.eval ν ∧ ∀ y, y ≠ x → ν' y = ν y
  -- `⟦x := *⟧ = {(ν,ν') | ν'(y) = ν(y) for all y ≠ x}` (x arbitrary).
  | .assignAny x, ν, ν' =>
      ∀ y, y ≠ x → ν' y = ν y
  /- `⟦{x⃗' = θ⃗} & ψ⟧`. Vector ODE, the three required parts:

  * **(a) Simultaneous derivatives** — for *every* equation `(x,θ) ∈ sys`, the
    trajectory's `x`-component has derivative `θ` at every `t ∈ [0,r]`. Conjunctive
    per equation, so a duplicated `x'` demands two derivatives of `Φ·x` at once →
    unsatisfiable unless the terms agree (malformed systems self-neutralize).
  * **(b) Masking** — every variable *not* bound by `sys` is held at its initial
    value throughout `[0,r]`. Without this, `{x'=1}&⊤` could move `y` freely,
    breaking frame properties. Matches Isabelle `mk_v` (off `semBV`) and Coq-dL
    `equal_states_except (ode_footprint)`.
  * **(c) Domain throughout** — `Φ t ∈ ⟦ψ⟧` for *all* `t ∈ [0,r]`, not just the
    endpoints (Fig 2: "for all of that duration").

  Plus init/endpoint/`r ≥ 0`: `Φ 0 = ν`, `Φ r = ν'`, `0 ≤ r`.

  NOTE: (a) uses `HasDerivWithinAt … (Set.Icc 0 r)`, the derivative *within* the
  interval, not the two-sided `HasDerivAt` written in the review gate. Reason:
  at the endpoints `0` and `r`, two-sided `HasDerivAt` demands differentiability
  in a full ℝ-neighborhood outside `[0,r]`, which is strictly stronger than Fig 2
  and both refs (Isabelle `solves_ode` uses `at t within {0..t}`), and would
  wrongly exclude solutions that exist on `[0,r]` but cannot be extended past `r`.
  Say the word to switch to two-sided `HasDerivAt` instead.

  NOTE: derivatives are taken *per scalar component* `fun s => Φ s x : ℝ → ℝ`, so
  `State V = V → ℝ` need not be a normed space — this is why we do not use
  Mathlib `IsIntegralCurveOn` (which wants the ambient space normed; `V → ℝ` is
  not, for arbitrary `V`). -/
  | .ode sys ψ, ν, ν' =>
      ∃ (r : ℝ) (Φ : ℝ → State V),
        0 ≤ r ∧ Φ 0 = ν ∧ Φ r = ν' ∧
        -- (a) simultaneous derivatives, all equations at once
        (∀ t ∈ Set.Icc (0:ℝ) r, ∀ p ∈ sys,
            HasDerivWithinAt (fun s => Φ s p.1) (p.2.eval (Φ t)) (Set.Icc 0 r) t) ∧
        -- (b) masking: non-bound variables held constant
        (∀ t ∈ Set.Icc (0:ℝ) r, ∀ x, x ∉ sys.bound → Φ t x = ν x) ∧
        -- (c) evolution domain holds throughout
        (∀ t ∈ Set.Icc (0:ℝ) r, Formula.sat ψ (Φ t))
  -- `⟦?ϕ⟧ = {(ν,ν) | ν ∈ ⟦ϕ⟧}` — no state change, precondition `ϕ`.
  | .test ϕ, ν, ν' =>
      ν = ν' ∧ Formula.sat ϕ ν
  -- `⟦α;β⟧ = {(ν,ν') | ∃ μ, (ν,μ) ∈ ⟦α⟧ ∧ (μ,ν') ∈ ⟦β⟧}`.
  | .seq α β, ν, ν' =>
      ∃ μ, Program.sem α ν μ ∧ Program.sem β μ ν'
  -- `⟦α ∪ β⟧ = ⟦α⟧ ∪ ⟦β⟧`.
  | .choice α β, ν, ν' =>
      Program.sem α ν ν' ∨ Program.sem β ν ν'
  -- `⟦α*⟧ = ⟦α⟧*`, the reflexive-transitive closure (loop induction: M4).
  | .star α, ν, ν' =>
      Relation.ReflTransGen (Program.sem α) ν ν'

/-- Formula satisfaction `⟦ϕ⟧`, as a predicate `State V → Prop`
(Fig 2, formula semantics). `Formula.sat ϕ ν` means `ν ∈ ⟦ϕ⟧`. -/
def Formula.sat {V : Type*} : Formula V → State V → Prop
  -- `⟦⊤⟧ = STA`.
  | .tt, _ => True
  -- `⟦θ ∼ δ⟧ = {ν | νJθK ∼ νJδK}`.
  | .cmp op a b, ν => op.interp (a.eval ν) (b.eval ν)
  -- `⟦¬ϕ⟧ = STA \ ⟦ϕ⟧`.
  | .neg ϕ, ν => ¬ Formula.sat ϕ ν
  -- `⟦ϕ ∧ ψ⟧ = ⟦ϕ⟧ ∩ ⟦ψ⟧`.
  | .and ϕ ψ, ν => Formula.sat ϕ ν ∧ Formula.sat ψ ν
  -- `⟦∀x. ϕ⟧ = ⟦[x := *]ϕ⟧` (Fig 2). Holds at `ν` iff `ϕ` holds at every state
  -- agreeing with `ν` off `x`. Avoids `Function.update`, hence no `DecidableEq V`.
  | .all x ϕ, ν =>
      ∀ ν' : State V, (∀ y, y ≠ x → ν' y = ν y) → Formula.sat ϕ ν'
  -- `⟦[α]ϕ⟧ = {ν | ∀ ν', (ν,ν') ∈ ⟦α⟧ → ν' ∈ ⟦ϕ⟧}`.
  | .box α ϕ, ν =>
      ∀ ν', Program.sem α ν ν' → Formula.sat ϕ ν'

end

/-! ## Derived connectives (abbreviations, Fig 2) — not constructors -/

namespace Formula

variable {V : Type*}

/-- `⊥ := ¬⊤`. -/
def fls : Formula V := neg tt
/-- `ϕ ∨ ψ := ¬(¬ϕ ∧ ¬ψ)`. -/
def or (ϕ ψ : Formula V) : Formula V := neg (and (neg ϕ) (neg ψ))
/-- `ϕ → ψ := ¬ϕ ∨ ψ`. -/
def imp (ϕ ψ : Formula V) : Formula V := or (neg ϕ) ψ
/-- `ϕ ↔ ψ := (ϕ → ψ) ∧ (ψ → ϕ)`. -/
def iff (ϕ ψ : Formula V) : Formula V := and (imp ϕ ψ) (imp ψ ϕ)
/-- `∃x. ϕ := ¬∀x. ¬ϕ`. -/
def ex (x : V) (ϕ : Formula V) : Formula V := neg (all x (neg ϕ))
/-- Diamond `⟨α⟩ϕ := ¬[α]¬ϕ` (Fig 2). -/
def diamond (α : Program V) (ϕ : Formula V) : Formula V := neg (box α (neg ϕ))

/-- Validity: `ϕ` holds in every state. -/
def valid (ϕ : Formula V) : Prop := ∀ ν, sat ϕ ν

end Formula

end DL
