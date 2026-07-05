/-
Copyright (c) 2026 dL-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: dL-lean contributors
-/
import DLLean.Semantics

/-!
# Basic metatheory (Milestone 3)

Sanity / non-vacuity validities exercising the M2 semantics:

* `box_test`   — `[?ϕ]ψ ↔ (ϕ → ψ)`
* `box_seq`    — `[α;β]ϕ ↔ [α][β]ϕ`
* `box_choice` — `[α ∪ β]ϕ ↔ [α]ϕ ∧ [β]ϕ`
* `diamond_sem`— `⟨α⟩ϕ ↔ ∃ ν', (ν,ν') ∈ ⟦α⟧ ∧ ϕ ν'`  (the content of `⟨α⟩ϕ = ¬[α]¬ϕ`)
* `ode_line_reach` — a concrete ODE: `{x' = 1}` reaches `x + r` while freezing `y`.

The four equivalences are yours to drive (learning mode): each has a `sorry`
plus a tactic sketch. The unfolding lemmas below and the ODE witness are provided.
-/

namespace DL

variable {V : Type*}

/-! ## Definitional unfolding lemmas

`Program.sem` / `Formula.sat` are structural recursions, so each constructor case
holds by `Iff.rfl`. These `@[simp]` lemmas let the metatheory proofs rewrite a
modality into its meaning without `unfold`. -/

@[simp] theorem sem_test (ϕ : Formula V) (ν ν' : State V) :
    Program.sem (.test ϕ) ν ν' ↔ (ν = ν' ∧ Formula.sat ϕ ν) := Iff.rfl

@[simp] theorem sem_seq (α β : Program V) (ν ν' : State V) :
    Program.sem (.seq α β) ν ν' ↔ ∃ μ, Program.sem α ν μ ∧ Program.sem β μ ν' := Iff.rfl

@[simp] theorem sem_choice (α β : Program V) (ν ν' : State V) :
    Program.sem (.choice α β) ν ν' ↔ Program.sem α ν ν' ∨ Program.sem β ν ν' := Iff.rfl

@[simp] theorem sat_and (ϕ ψ : Formula V) (ν : State V) :
    Formula.sat (.and ϕ ψ) ν ↔ Formula.sat ϕ ν ∧ Formula.sat ψ ν := Iff.rfl

@[simp] theorem sat_neg (ϕ : Formula V) (ν : State V) :
    Formula.sat (.neg ϕ) ν ↔ ¬ Formula.sat ϕ ν := Iff.rfl

@[simp] theorem sat_box (α : Program V) (ϕ : Formula V) (ν : State V) :
    Formula.sat (.box α ϕ) ν ↔ ∀ ν', Program.sem α ν ν' → Formula.sat ϕ ν' := Iff.rfl

/-- `⟨α⟩ϕ` unfolded one level (`diamond` is `¬[α]¬ϕ` by definition). -/
theorem sat_diamond (α : Program V) (ϕ : Formula V) (ν : State V) :
    Formula.sat (.diamond α ϕ) ν ↔ ¬ ∀ ν', Program.sem α ν ν' → ¬ Formula.sat ϕ ν' :=
  Iff.rfl

/-! ## The four validities — YOUR proofs (scaffolded) -/

/-- `[?ϕ]ψ ↔ (ϕ → ψ)`.

Sketch: `simp only [sat_box, sem_test]`, then the antecedent `ν = ν' ∧ ϕ ν`
splits. `constructor`; forward feeds `⟨rfl, hϕ⟩`; backward `rintro h ν' ⟨rfl, hϕ⟩`. -/
theorem box_test (ϕ ψ : Formula V) (ν : State V) :
    Formula.sat (.box (.test ϕ) ψ) ν ↔ (Formula.sat ϕ ν → Formula.sat ψ ν) := by
  simp only [sat_box, sem_test]
  constructor;
  · intro h hϕ; exact h ν ⟨rfl, hϕ⟩
  · rintro h ν' ⟨rfl, hϕ⟩; exact h hϕ


/-- `[α;β]ϕ ↔ [α][β]ϕ`.

Sketch: `simp only [sat_box, sem_seq]`. LHS quantifies over `ν'` with a witness
`μ`; RHS quantifies `μ` then `ν'`. `constructor` and shuffle the binders:
forward `intro h μ hα ν' hβ; exact h ν' ⟨μ, hα, hβ⟩`; backward
`rintro h ν' ⟨μ, hα, hβ⟩; exact h μ hα ν' hβ`. -/
theorem box_seq (α β : Program V) (ϕ : Formula V) (ν : State V) :
    Formula.sat (.box (.seq α β) ϕ) ν ↔ Formula.sat (.box α (.box β ϕ)) ν := by
  simp only [sat_box, sem_seq]
  constructor;
  · intro h μ hα ν' hβ; exact h ν' ⟨μ, hα, hβ⟩
  · rintro h ν' ⟨μ, hα, hβ⟩; exact h μ hα ν' hβ

/-- `[α ∪ β]ϕ ↔ [α]ϕ ∧ [β]ϕ`.

Sketch: `simp only [sat_box, sem_choice, sat_and]`, then it's
`(∀ ν', P ∨ Q → R) ↔ (∀ ν', P → R) ∧ (∀ ν', Q → R)`. `constructor`; forward
returns `⟨fun ν' h => .., fun ν' h => ..⟩` feeding `Or.inl/Or.inr`; backward
`rintro ⟨hα, hβ⟩ ν' (h | h)`. Or try `aesop` / `tauto` after the `simp`. -/
theorem box_choice (α β : Program V) (ϕ : Formula V) (ν : State V) :
    Formula.sat (.box (.choice α β) ϕ) ν ↔
      Formula.sat (.box α ϕ) ν ∧ Formula.sat (.box β ϕ) ν := by
  simp only [sat_box, sem_choice]
  constructor;
  · intro h; exact ⟨fun ν' hα => h ν' (Or.inl hα), fun ν' hβ => h ν' (Or.inr hβ)⟩
  · rintro ⟨hα, hβ⟩ ν' (h | h); exacts [hα ν' h, hβ ν' h]

/-- `⟨α⟩ϕ ↔ ∃ ν', (ν,ν') ∈ ⟦α⟧ ∧ ϕ ν'` — the meaning of `⟨α⟩ϕ = ¬[α]¬ϕ`.

Sketch (uses classical logic): `rw [sat_diamond]`, then `push_neg`. `push_neg`
turns `¬ ∀ ν', sem → ¬ ϕ` into `∃ ν', sem ∧ ϕ` directly. Should close with `rfl`
or need no more. (`Classical` is already available via Mathlib.) -/
theorem diamond_sem (α : Program V) (ϕ : Formula V) (ν : State V) :
    Formula.sat (.diamond α ϕ) ν ↔ ∃ ν', Program.sem α ν ν' ∧ Formula.sat ϕ ν' := by
  rw [sat_diamond]
  push Not
  rfl

/-! ## Concrete ODE example (witness constructed together)

Two variables `Bool`: `true` evolves under `x' = 1`, `false` is untouched.
From any `ν` and any duration `r ≥ 0`, the ODE reaches the state that adds `r`
to the `true`-coordinate and leaves `false` fixed. The witness solution is
`Φ t = (fun b => bif b then ν true + t else ν false)` — a straight line in the
`true` coordinate, constant in `false`. This exercises all three ODE clauses:
(a) the derivative on `true`, (b) masking `false`, (c) the (trivial) domain `⊤`. -/
theorem ode_line_reach (ν : State Bool) (r : ℝ) (hr : 0 ≤ r) :
    Program.sem (.ode [(true, .const 1)] .tt) ν
      (fun b => bif b then ν true + r else ν false) := by
  -- Provide duration r and the straight-line witness Φ.
  refine ⟨r, (fun t b => bif b then ν true + t else ν false), hr, ?_, ?_, ?_, ?_, ?_⟩
  · -- Φ 0 = ν  (adding 0 in the `true` coordinate)
    funext b; cases b <;> simp
  · -- Φ r = ν'  (definitionally the target)
    rfl
  · -- (a) derivative: on the single equation (true, 1),
    --     (fun s => ν true + s) has derivative 1 within [0,r].
    intro t _ p hp
    rw [List.mem_singleton] at hp; subst hp
    change HasDerivWithinAt (fun s => ν true + s) 1 (Set.Icc 0 r) t
    exact ((hasDerivAt_id t).const_add (ν true)).hasDerivWithinAt
  · -- (b) masking: the only non-bound variable is `false`, held at ν false.
    intro t _ x hx
    cases x with
    | false => rfl
    | true => simp [ODESystem.bound] at hx
  · -- (c) domain ⊤ holds everywhere.
    intro t _; trivial

end DL
