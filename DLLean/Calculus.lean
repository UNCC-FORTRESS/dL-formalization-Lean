/-
Copyright (c) 2026 dL-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: dL-lean contributors
-/
import DLLean.Loop

/-!
# dL proof calculus — exploratory scout (bonus, not a required milestone)

Soundness of the dL axioms/rules that need **no** uniform substitution and **no**
static semantics (free/bound-variable analysis). Everything here is proven against
the M2 semantics directly.

Already proven elsewhere (the compositional box axioms):
* `[?ϕ]ψ ↔ (ϕ → ψ)`      — `box_test`        (M3)
* `[α;β]ϕ ↔ [α][β]ϕ`      — `box_seq`         (M3)
* `[α∪β]ϕ ↔ [α]ϕ ∧ [β]ϕ`  — `box_choice`      (M3)
* `[α*]ϕ ↔ ϕ ∧ [α][α*]ϕ`  — `sat_box_star_iff`(M4)
* loop induction          — `sat_box_star_of_inv` / `loop_rule` (M4)

Added here:
* `K_axiom`        — `[α](ϕ→ψ) → ([α]ϕ → [α]ψ)`   (modal K)
* `necessitation`  — `⊢ ϕ  ⟹  ⊢ [α]ϕ`            (Gödel generalization)
* `box_mono`       — monotonicity of `[α]` under `ϕ → ψ`
* `sat_box_assign` — semantic assignment `[x:=θ]ϕ ↔ ϕ(ν[x↦⟦θ⟧])`

**Deliberately out of scope for this scout** (need machinery we have not built):
* `[:=]` as *syntactic* substitution `[x:=θ]p(x) ↔ p(θ)` — needs a substitution
  operation on formulas.
* `V` (vacuous) `ϕ → [α]ϕ`, and the differential axioms `DW/DC/DE/DI/DG` — need
  the static (free/bound-variable) semantics.
* The uniform-substitution rule — the large layer (≈2× the semantics in Coq-dL).

`sat_box_assign` gives the *semantic* content of `[:=]`; the syntactic
substitution axiom is what would need the substitution layer.
-/

namespace DL

variable {V : Type*}

/-- `⟦x := θ⟧` unfolded. -/
@[simp] theorem sem_assign (x : V) (θ : Term V) (ν ν' : State V) :
    Program.sem (.assign x θ) ν ν' ↔
      (ν' x = θ.eval ν ∧ ∀ y, y ≠ x → ν' y = ν y) := Iff.rfl

/-- `⟦x := *⟧` unfolded. -/
@[simp] theorem sem_assignAny (x : V) (ν ν' : State V) :
    Program.sem (.assignAny x) ν ν' ↔ (∀ y, y ≠ x → ν' y = ν y) := Iff.rfl

/-- **Modal K.** `[α]` distributes over implication. -/
theorem K_axiom (α : Program V) (ϕ ψ : Formula V) :
    Formula.valid (.imp (.box α (.imp ϕ ψ)) (.imp (.box α ϕ) (.box α ψ))) := by
  intro ν
  simp only [sat_imp, sat_box]
  intro himp hϕ ν' hν'
  exact himp ν' hν' (hϕ ν' hν')

/-- **Gödel generalization / necessitation.** A valid formula is valid after any box. -/
theorem necessitation (α : Program V) {ϕ : Formula V} (h : Formula.valid ϕ) :
    Formula.valid (.box α ϕ) := by
  intro ν ν' _
  exact h ν'

/-- **Box monotonicity.** If `ϕ → ψ` pointwise, then `[α]ϕ → [α]ψ` pointwise. -/
theorem box_mono (α : Program V) {ϕ ψ : Formula V}
    (h : ∀ ν, Formula.sat ϕ ν → Formula.sat ψ ν) :
    ∀ ν, Formula.sat (.box α ϕ) ν → Formula.sat (.box α ψ) ν := by
  intro ν hbox ν' hν'
  exact h ν' (hbox ν' hν')

/-- **Semantic assignment axiom.** `[x := θ]ϕ` holds at `ν` iff `ϕ` holds at the
state `ν` updated so `x ↦ ⟦θ⟧ν`. This is the semantic content of `[:=]`; the
*syntactic* substitution form `[x:=θ]p(x) ↔ p(θ)` would need a substitution
operation on formulas (out of scope). -/
theorem sat_box_assign [DecidableEq V] (x : V) (θ : Term V) (ϕ : Formula V)
    (ν : State V) :
    Formula.sat (.box (.assign x θ) ϕ) ν ↔
      Formula.sat ϕ (Function.update ν x (θ.eval ν)) := by
  simp only [sat_box, sem_assign]
  constructor
  · intro h
    refine h _ ⟨Function.update_self x (θ.eval ν) ν, fun y hy => ?_⟩
    exact Function.update_of_ne hy (θ.eval ν) ν
  · intro h ν' hν'
    have hstate : ν' = Function.update ν x (θ.eval ν) := by
      funext y
      by_cases hyx : y = x
      · subst hyx; rw [hν'.1, Function.update_self]
      · rw [hν'.2 y hyx, Function.update_of_ne hyx]
    rw [hstate]; exact h

end DL
