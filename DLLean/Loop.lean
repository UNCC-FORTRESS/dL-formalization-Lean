/-
Copyright (c) 2026 dL-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: dL-lean contributors
-/
import DLLean.Metatheory

/-!
# Loop semantics and induction (Milestone 4)

`⟦α*⟧` is already the reflexive-transitive closure of `⟦α⟧` (Fig 2, defined in
`Semantics.lean` as `Relation.ReflTransGen`). Here we expose it and prove the two
loop principles the downstream work needs:

* `sat_box_star_of_inv` — the **loop-induction principle**: if `ϕ` is preserved by
  one step (`ϕ → [α]ϕ`), then it is preserved by the loop (`ϕ → [α*]ϕ`).
* `loop_rule` — the same, packaged in dL-calculus `valid` form.
* `sat_box_star_iff` — the loop **unfolding** `[α*]ϕ ↔ ϕ ∧ [α][α*]ϕ`.
-/

namespace DL

variable {V : Type*}

/-- `⟦α*⟧` is the reflexive-transitive closure of `⟦α⟧`. -/
@[simp] theorem sem_star (α : Program V) (ν ν' : State V) :
    Program.sem (.star α) ν ν' ↔ Relation.ReflTransGen (Program.sem α) ν ν' := Iff.rfl

/-- `ϕ → ψ` satisfaction (classical; `imp` is derived from `¬`/`∧`). -/
@[simp] theorem sat_imp (ϕ ψ : Formula V) (ν : State V) :
    Formula.sat (.imp ϕ ψ) ν ↔ (Formula.sat ϕ ν → Formula.sat ψ ν) := by
  simp only [Formula.imp, Formula.or, sat_neg, sat_and]
  tauto

/-- **Loop-induction principle.** If `ϕ` is an invariant of `α` (`ϕ → [α]ϕ` holds
pointwise), then it is an invariant of the loop `α*`. Proof: induction on the
reflexive-transitive closure — `refl` gives `ϕ` at the start, and each `tail`
step applies the one-step invariance. -/
theorem sat_box_star_of_inv {α : Program V} {ϕ : Formula V}
    (hinv : ∀ ν, Formula.sat ϕ ν → Formula.sat (.box α ϕ) ν) :
    ∀ ν, Formula.sat ϕ ν → Formula.sat (.box (.star α) ϕ) ν := by
  intro ν hϕ ν' hstar
  induction hstar with
  | refl => exact hϕ
  | tail _ hlast ih => exact hinv _ ih _ hlast

/-- **Loop rule** (dL-calculus form): from validity of `ϕ → [α]ϕ`, conclude
validity of `ϕ → [α*]ϕ`. -/
theorem loop_rule {α : Program V} {ϕ : Formula V}
    (h : Formula.valid (.imp ϕ (.box α ϕ))) :
    Formula.valid (.imp ϕ (.box (.star α) ϕ)) := by
  intro ν
  rw [sat_imp]
  intro hϕ
  refine sat_box_star_of_inv (fun μ hμ => ?_) ν hϕ
  exact (sat_imp _ _ _).mp (h μ) hμ

/-- **Loop unfolding** `[α*]ϕ ↔ ϕ ∧ [α][α*]ϕ`. Reflexivity gives the `ϕ`
conjunct; the head/tail split of the closure gives the `[α][α*]ϕ` conjunct. -/
theorem sat_box_star_iff {α : Program V} {ϕ : Formula V} (ν : State V) :
    Formula.sat (.box (.star α) ϕ) ν ↔
      Formula.sat ϕ ν ∧ Formula.sat (.box α (.box (.star α) ϕ)) ν := by
  simp only [sat_box, sem_star]
  constructor
  · intro h
    exact ⟨h ν .refl, fun μ hμ ν' hν' => h ν' (Relation.ReflTransGen.head hμ hν')⟩
  · rintro ⟨h0, hstep⟩ ν' hν'
    rcases Relation.ReflTransGen.cases_head hν' with rfl | ⟨μ, hfirst, htail⟩
    · exact h0
    · exact hstep μ hfirst ν' htail

end DL
