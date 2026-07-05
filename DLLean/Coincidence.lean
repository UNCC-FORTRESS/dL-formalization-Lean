/-
Copyright (c) 2026 dL-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: dL-lean contributors
-/
import DLLean.Static
import DLLean.Loop

/-!
# Coincidence and bound-effect (static-semantics milestone)

The standard free-variable coincidence and bound-effect metatheory.
Single fixed interpretation (empty signature), differential-variable-free state.

* `Term.coincidence`     — a term's value depends only on its free variables.
* `Formula.coincidence` / `Program.coincidence` — mutual; programs carry the
  **frame-aware** `V ∪ MBV(α)` output-agreement conjunct.
* `Program.bound_effect` — a run changes only bound variables.
* `V_axiom`, `DW` — sanity consumers.
-/

namespace DL

open Set

variable {V : Type*}

/-- **Coincidence for terms**: equal on `FV(θ)` ⟹ equal values. -/
theorem Term.coincidence (θ : Term V) {ν w : State V}
    (h : Set.EqOn ν w θ.fv) : θ.eval ν = θ.eval w := by
  induction θ with
  | var x => exact h (by simp [Term.fv])
  | const c => rfl
  | binop op a b iha ihb =>
      simp only [Term.eval]
      rw [iha (h.mono (by simp [Term.fv])), ihb (h.mono (by simp [Term.fv]))]

/-! ## Coincidence for formulas and programs (mutual) -/

mutual

/-- **Coincidence for formulas**. -/
theorem Formula.coincidence (ϕ : Formula V) {ν w : State V}
    (h : Set.EqOn ν w ϕ.fv) : ϕ.sat ν ↔ ϕ.sat w := by
  classical
  cases ϕ with
  | tt => exact Iff.rfl
  | cmp o a b =>
      simp only [Formula.fv] at h
      simp only [Formula.sat,
        Term.coincidence a (h.mono subset_union_left),
        Term.coincidence b (h.mono subset_union_right)]
  | neg ψ =>
      simp only [Formula.fv] at h
      simp only [Formula.sat, Formula.coincidence ψ h]
  | and ψ χ =>
      simp only [Formula.fv] at h
      simp only [Formula.sat, Formula.coincidence ψ (h.mono subset_union_left),
        Formula.coincidence χ (h.mono subset_union_right)]
  | all x ψ =>
      simp only [Formula.fv] at h
      simp only [Formula.sat]
      constructor
      · intro hL ν' hν'
        have hsat := hL (Function.update ν x (ν' x)) (fun y hy => Function.update_of_ne hy _ _)
        refine (Formula.coincidence ψ ?_).mp hsat
        intro z hz
        by_cases hzx : z = x
        · subst hzx; simp [Function.update_self]
        · rw [Function.update_of_ne hzx, h ⟨hz, by simpa using hzx⟩, hν' z hzx]
      · intro hR ν' hν'
        have hsat := hR (Function.update w x (ν' x)) (fun y hy => Function.update_of_ne hy _ _)
        refine (Formula.coincidence ψ ?_).mpr hsat
        intro z hz
        by_cases hzx : z = x
        · subst hzx; simp [Function.update_self]
        · rw [Function.update_of_ne hzx, ← h ⟨hz, by simpa using hzx⟩, hν' z hzx]
  | box α ψ =>
      simp only [Formula.fv] at h
      simp only [Formula.sat]
      constructor
      · intro hL ω₂ hω₂
        obtain ⟨ω, hωrun, hωω₂⟩ :=
          Program.coincidence α subset_union_left h.symm hω₂
        refine (Formula.coincidence ψ ?_).mp (hL ω hωrun)
        intro z hz
        refine (hωω₂ ?_).symm
        by_cases hzm : z ∈ α.mbv
        · exact Or.inr hzm
        · exact Or.inl (Or.inr ⟨hz, hzm⟩)
      · intro hR ω hωrun
        obtain ⟨ω₂, hω₂run, hωω₂⟩ :=
          Program.coincidence α subset_union_left h hωrun
        refine (Formula.coincidence ψ ?_).mpr (hR ω₂ hω₂run)
        intro z hz
        apply hωω₂
        by_cases hzm : z ∈ α.mbv
        · exact Or.inr hzm
        · exact Or.inl (Or.inr ⟨hz, hzm⟩)

/-- **Coincidence for programs**: equal on `V ⊇ FV(α)`
and `(ν,ω) ∈ ⟦α⟧` gives a matching run from `w` whose end agrees with `ω` on
`V ∪ MBV(α)`. -/
theorem Program.coincidence (α : Program V) {ν w : State V} {W : Set V}
    (hsub : α.fv ⊆ W) (hag : Set.EqOn ν w W) {ω : State V}
    (hrun : Program.sem α ν ω) :
    ∃ ω₂, Program.sem α w ω₂ ∧ Set.EqOn ω ω₂ (W ∪ α.mbv) := by
  classical
  cases α with
  | assign x θ =>
      simp only [Program.fv] at hsub
      simp only [Program.mbv]
      obtain ⟨hωx, hωy⟩ := hrun
      refine ⟨Function.update w x (θ.eval w),
        ⟨Function.update_self _ _ _, fun y hy => Function.update_of_ne hy _ _⟩, ?_⟩
      intro z hz
      by_cases hzx : z = x
      · subst hzx
        rw [hωx, Function.update_self]
        exact Term.coincidence θ (hag.mono hsub)
      · rw [hωy z hzx, Function.update_of_ne hzx]
        rcases hz with hzW | hzm
        · exact hag hzW
        · exact absurd hzm (by simpa using hzx)
  | assignAny x =>
      simp only [Program.mbv]
      refine ⟨Function.update w x (ω x),
        (fun y hy => Function.update_of_ne hy _ _), ?_⟩
      intro z hz
      by_cases hzx : z = x
      · subst hzx; rw [Function.update_self]
      · rw [Function.update_of_ne hzx]
        rcases hz with hzW | hzm
        · rw [hrun z hzx]; exact hag hzW
        · exact absurd hzm (by simpa using hzx)
  | test ϕ =>
      simp only [Program.fv] at hsub
      simp only [Program.mbv, union_empty]
      obtain ⟨heq, hsat⟩ := hrun
      refine ⟨w, ⟨rfl, (Formula.coincidence ϕ (hag.mono hsub)).mp hsat⟩, ?_⟩
      intro z hz; rw [← heq]; exact hag hz
  | ode sys ψ =>
      simp only [Program.fv] at hsub
      simp only [Program.mbv]
      obtain ⟨r, Φ, hr, hΦ0, hΦr, hderiv, hmask, hdom⟩ := hrun
      have hbW : sys.boundSet ⊆ W :=
        (subset_union_left.trans subset_union_left).trans hsub
      have hrW : sys.readVars ⊆ W :=
        (subset_union_right.trans subset_union_left).trans hsub
      have hψW : Formula.fv ψ ⊆ W := subset_union_right.trans hsub
      set Ψ : ℝ → State V := fun t y => if y ∈ sys.bound then Φ t y else w y with hΨ
      have hagt : ∀ t, t ∈ Set.Icc (0:ℝ) r → Set.EqOn (Φ t) (Ψ t) W := by
        intro t ht z hz
        by_cases hzb : z ∈ sys.bound
        · simp only [hΨ, if_pos hzb]
        · simp only [hΨ, if_neg hzb]
          rw [hmask t ht z hzb]; exact hag hz
      refine ⟨Ψ r, ⟨r, Ψ, hr, ?_, rfl, ?_, ?_, ?_⟩, ?_⟩
      · -- Ψ 0 = w
        funext y
        by_cases hyb : y ∈ sys.bound
        · simp only [hΨ, if_pos hyb, hΦ0]; exact hag (hbW hyb)
        · simp only [hΨ, if_neg hyb]
      · -- (a) derivatives
        intro t ht p hp
        have hp1b : p.1 ∈ sys.bound := List.mem_map_of_mem hp
        have hfun : (fun s => Ψ s p.1) = (fun s => Φ s p.1) := by
          funext s; simp only [hΨ, if_pos hp1b]
        rw [hfun]
        have hval : p.2.eval (Ψ t) = p.2.eval (Φ t) :=
          Term.coincidence p.2 (fun z hz => ((hagt t ht) (hrW ⟨p, hp, hz⟩)).symm)
        rw [hval]; exact hderiv t ht p hp
      · -- (b) masking
        intro t _ x hx; simp only [hΨ, if_neg hx]
      · -- (c) domain
        intro t ht
        exact (Formula.coincidence ψ ((hagt t ht).mono hψW)).mp (hdom t ht)
      · -- output agreement on W ∪ sys.boundSet
        intro z hz
        by_cases hzb : z ∈ sys.bound
        · simp only [hΨ, if_pos hzb]; exact (congrFun hΦr z).symm
        · have hzW : z ∈ W := by
            rcases hz with h1 | h2
            · exact h1
            · exact absurd (by simpa [ODESystem.boundSet] using h2) hzb
          simp only [hΨ, if_neg hzb]
          rw [← congrFun hΦr z, hmask r (right_mem_Icc.mpr hr) z hzb]; exact hag hzW
  | seq a b =>
      simp only [Program.fv] at hsub
      simp only [Program.mbv]
      obtain ⟨μ, hνμ, hμω⟩ := hrun
      have hsuba : a.fv ⊆ W := subset_union_left.trans hsub
      obtain ⟨μ₂, haw, hμμ₂⟩ := Program.coincidence a hsuba hag hνμ
      have hsubb : b.fv ⊆ W ∪ a.mbv := by
        intro z hz
        by_cases hzm : z ∈ a.mbv
        · exact Or.inr hzm
        · exact Or.inl (hsub (Or.inr ⟨hz, hzm⟩))
      obtain ⟨ω₂, hbw, hωω₂⟩ := Program.coincidence b hsubb hμμ₂ hμω
      refine ⟨ω₂, ⟨μ₂, haw, hbw⟩, ?_⟩
      intro z hz
      apply hωω₂
      rcases hz with hzW | hzab
      · exact Or.inl (Or.inl hzW)
      · rcases hzab with hza | hzb
        · exact Or.inl (Or.inr hza)
        · exact Or.inr hzb
  | choice a b =>
      simp only [Program.fv] at hsub
      simp only [Program.mbv]
      rcases hrun with hA | hB
      · have hsuba : a.fv ⊆ W := subset_union_left.trans hsub
        obtain ⟨ω₂, haw, hωω₂⟩ := Program.coincidence a hsuba hag hA
        refine ⟨ω₂, Or.inl haw, ?_⟩
        intro z hz; apply hωω₂
        rcases hz with hzW | hzab
        · exact Or.inl hzW
        · exact Or.inr hzab.1
      · have hsubb : b.fv ⊆ W := subset_union_right.trans hsub
        obtain ⟨ω₂, hbw, hωω₂⟩ := Program.coincidence b hsubb hag hB
        refine ⟨ω₂, Or.inr hbw, ?_⟩
        intro z hz; apply hωω₂
        rcases hz with hzW | hzab
        · exact Or.inl hzW
        · exact Or.inr hzab.2
  | star a =>
      simp only [Program.fv] at hsub
      simp only [Program.mbv, union_empty]
      induction hrun with
      | refl => exact ⟨w, Relation.ReflTransGen.refl, hag⟩
      | tail _ hlast ih =>
          obtain ⟨μ₂, hμ₂path, hμμ₂⟩ := ih
          obtain ⟨ω₂, haw, hωω₂⟩ := Program.coincidence a hsub hμμ₂ hlast
          exact ⟨ω₂, hμ₂path.tail haw, fun z hz => hωω₂ (Or.inl hz)⟩

end

/-- **Bound effect**: a run of `α` changes only its bound variables. -/
theorem Program.bound_effect (α : Program V) :
    ∀ {ν ω : State V}, Program.sem α ν ω → ∀ x, x ∉ α.bv → ν x = ω x := by
  intro ν ω hrun x hx
  cases α with
  | assign y θ =>
      obtain ⟨_, hωy⟩ := hrun
      exact (hωy x (by simpa [Program.bv] using hx)).symm
  | assignAny y =>
      exact (hrun x (by simpa [Program.bv] using hx)).symm
  | test ϕ =>
      obtain ⟨heq, _⟩ := hrun; rw [heq]
  | ode sys ψ =>
      obtain ⟨r, Φ, hr, hΦ0, hΦr, _, hmask, _⟩ := hrun
      have hxb : x ∉ sys.bound := by simpa [Program.bv, ODESystem.boundSet] using hx
      rw [← hΦ0, ← hΦr, hmask 0 (left_mem_Icc.mpr hr) x hxb,
        hmask r (right_mem_Icc.mpr hr) x hxb]
  | seq a b =>
      obtain ⟨μ, ha, hb⟩ := hrun
      have hxa : x ∉ a.bv := fun h => hx (Or.inl h)
      have hxb : x ∉ b.bv := fun h => hx (Or.inr h)
      rw [Program.bound_effect a ha x hxa, Program.bound_effect b hb x hxb]
  | choice a b =>
      have hxa : x ∉ a.bv := fun h => hx (Or.inl h)
      have hxb : x ∉ b.bv := fun h => hx (Or.inr h)
      rcases hrun with h | h
      · exact Program.bound_effect a h x hxa
      · exact Program.bound_effect b h x hxb
  | star a =>
      have hxa : x ∉ a.bv := by simpa [Program.bv] using hx
      induction hrun with
      | refl => rfl
      | tail _ hlast ih => rw [ih, Program.bound_effect a hlast x hxa]

/-! ## Sanity consumers -/

/-- **V (vacuous) axiom**: if `ϕ` reads no variable `α` writes, it survives `α`. -/
theorem V_axiom {α : Program V} {ϕ : Formula V}
    (hdisj : Formula.fv ϕ ∩ α.bv = ∅) {ν : State V} (hϕ : Formula.sat ϕ ν) :
    Formula.sat (Formula.box α ϕ) ν := by
  intro ω hω
  refine (Formula.coincidence ϕ (fun z hz => ?_)).mp hϕ
  refine Program.bound_effect α hω z (fun hzb => ?_)
  have : z ∈ Formula.fv ϕ ∩ α.bv := ⟨hz, hzb⟩
  rw [hdisj] at this; exact this

/-- **DW (differential weakening)**: the evolution domain holds after the ODE. -/
theorem DW {sys : ODESystem V} {ψ : Formula V} {ν : State V} :
    Formula.sat (Formula.box (Program.ode sys ψ) ψ) ν := by
  intro ω hω
  obtain ⟨r, Φ, hr, _, hΦr, _, _, hdom⟩ := hω
  rw [← hΦr]; exact hdom r (right_mem_Icc.mpr hr)

end DL
