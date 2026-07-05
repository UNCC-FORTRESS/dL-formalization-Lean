/-
Copyright (c) 2026 dL-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: dL-lean contributors
-/
import DLLean.Semantics

/-!
# Static semantics — free, bound, must-bound variables (definitions for review)

Frame-aware schematic route: `FV`, `BV`, and `MBV`, following Platzer,
*A Complete Uniform Substitution Calculus for dL*, Def 8 (BV), Def 9 (MBV),
Def 10 (FV), and Lemma 4 (coincidence for programs). No uniform substitution,
no contexts, no substitution operator — `MBV` is included only for the precise,
frame-aware coincidence property (output agreement on `V ∪ MBV(α)`) that the
downstream relational / simulation-distance work needs.

Two deliberate divergences from Platzer, both sound in our setting:

* **(a) Collapsed `x'`.** Platzer's state carries differential variables, so
  `BV(x'=θ&ψ) = MBV = {x, x'}` and `FV` adds `{x}`. Our state is `V → ℝ` with no
  differential variables, so the `x'` coordinate is absent: `BV = MBV =
  sys.boundSet` (the `x`s), matching the M2 masking complement.
* **(b) Dropped `Σ`/`I = J`.** Platzer carries `I = J on Σ(·)` (agreement of
  uninterpreted function/predicate symbols). Our terms are `var | const | binop`
  and formulas have no uninterpreted predicates, so `Σ = ∅` everywhere and the
  `I = J` hypothesis is vacuous — omitted. Single fixed interpretation.

All sets are `Set V` (no `Finset`, no typeclass).
These definitions are the review gate — no lemmas are proved yet.
-/

namespace DL

variable {V : Type*}

/-- Free variables of a term (Def 10): the variables it reads. -/
def Term.fv : Term V → Set V
  | .var x => {x}
  | .const _ => ∅
  | .binop _ a b => a.fv ∪ b.fv

/-- Left-hand (evolving) variables of a vector ODE, as a `Set V` (= `sys.bound`). -/
def ODESystem.boundSet (sys : ODESystem V) : Set V := {x | x ∈ sys.bound}

/-- Variables read by a vector ODE's right-hand sides: free vars of every RHS. -/
def ODESystem.readVars (sys : ODESystem V) : Set V := {x | ∃ p ∈ sys, x ∈ Term.fv p.2}

/-! ## Bound and must-bound variables of programs (standalone recursions).

Neither is mutual with formulas: the formula-carrying program cases (`test`, ODE
domain) contribute no written variables, so both recurse on programs alone. -/

/-- Bound variables (Def 8): variables the program may write. -/
def Program.bv : Program V → Set V
  | .assign x _ => {x}
  | .assignAny x => {x}
  -- ODE-BV (GATE): LHS vars only. Platzer `BV(x'=θ&ψ) = {x,x'}`; the `x'`
  -- coordinate collapses in our differential-variable-free state.
  | .ode sys _ => sys.boundSet
  | .test _ => ∅
  | .seq α β => α.bv ∪ β.bv
  | .choice α β => α.bv ∪ β.bv
  | .star α => α.bv

/-- Must-bound variables (Def 9): variables written on *every* path. -/
def Program.mbv : Program V → Set V
  -- atomic HPs: MBV = BV (Def 9).
  | .assign x _ => {x}
  | .assignAny x => {x}
  -- ODE: MBV = BV = LHS vars (`{x,x'}` collapses to the `x`s, as for BV).
  | .ode sys _ => sys.boundSet
  | .test _ => ∅
  -- compositional: `;` unions, `∪` INTERSECTS (must-bound on both branches),
  -- `*` is empty (the loop body may run zero times).
  | .seq α β => α.mbv ∪ β.mbv
  | .choice α β => α.mbv ∩ β.mbv
  | .star _ => ∅

/-! ## Free variables of formulas and programs (mutually recursive, Def 10) -/

mutual

/-- Free variables of a program (Def 10): variables it may read. -/
def Program.fv : Program V → Set V
  -- `x := θ` reads `θ`, not `x`.
  | .assign _ θ => θ.fv
  -- `x := *` reads nothing.
  | .assignAny _ => ∅
  -- ODE-FV (GATE): evolving vars ∪ RHS free vars ∪ domain free vars.
  -- Platzer `FV(x'=θ&ψ) = {x} ∪ FV θ ∪ FV ψ`.
  | .ode sys ψ => sys.boundSet ∪ sys.readVars ∪ Formula.fv ψ
  | .test ϕ => Formula.fv ϕ
  -- seq-FV (GATE, REFINED): `FV(α) ∪ (FV(β) \ MBV(α))` — `β` runs after `α`, so
  -- `α`'s must-bound writes shadow `β`'s reads of them (Platzer Def 10).
  | .seq α β => α.fv ∪ (β.fv \ α.mbv)
  -- choice-FV: PLAIN union `FV(α) ∪ FV(β)` (Platzer Def 10). NOT refined with
  -- `\ MBV`: both branches run from the initial state, so nothing shadows their
  -- reads; subtracting would be unsound (it would drop genuinely-read variables).
  | .choice α β => α.fv ∪ β.fv
  | .star α => α.fv

/-- Free variables of a formula (Def 10). -/
def Formula.fv : Formula V → Set V
  | .tt => ∅
  | .cmp _ a b => a.fv ∪ b.fv
  | .neg ϕ => ϕ.fv
  | .and ϕ ψ => ϕ.fv ∪ ψ.fv
  -- `∀x. ϕ` binds `x`: `FV(∀x φ) = FV(φ) \ {x}`.
  | .all x ϕ => ϕ.fv \ {x}
  -- box-FV (GATE, REFINED): `FV(α) ∪ (FV(ϕ) \ MBV(α))` — must-bound writes of `α`
  -- shadow the postcondition's reads (Platzer Def 10). This precise form is what
  -- makes the frame-aware coincidence go through, and why we carry `MBV`.
  | .box α ϕ => α.fv ∪ (ϕ.fv \ α.mbv)

end

end DL
