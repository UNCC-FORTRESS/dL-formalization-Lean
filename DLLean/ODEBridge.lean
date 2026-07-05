/-
Copyright (c) 2026 dL-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: dL-lean contributors
-/
import DLLean.Semantics

/-!
# Bridge: per-component ODE semantics ↔ Mathlib `IsIntegralCurveOn`

Validation that the per-component `Program.sem` ODE case reaches Mathlib's ODE
metatheory. Under `[Fintype V]` (which makes `State V = V → ℝ` a complete normed
space, *without changing the type*) plus `[DecidableEq V]` and `sys.WellFormed`,
the transition relation `⟦{x⃗'=θ⃗}&ψ⟧` is equivalent to "there is an integral
curve of the assembled vector field `odeField sys`, staying in `ψ`".

The `←` direction recovers masking (non-bound variables constant) from the field
being `0` off the bound set, via `constant_of_derivWithin_zero` (derivative `0`
on the convex `Icc` ⟹ constant). `WellFormed` earns its keep in both directions:
`Nodup` on the left-hand variables is exactly what makes `ODESystem.rhs` return
the unique right-hand term for each bound variable (`rhs_eq_of_mem`).
-/

namespace DL

open Set

variable {V : Type*}

/-- The right-hand term assigned to variable `i` by the system, via first match.
On a `WellFormed` system this is *the* unique equation for `i` (`rhs_eq_of_mem`);
the `Term.const 0` default is unreachable for bound `i`. -/
def ODESystem.rhs [DecidableEq V] (sys : ODESystem V) (i : V) : Term V :=
  (sys.find? (fun p => decide (p.1 = i))).elim (Term.const 0) Prod.snd

/-- The assembled autonomous vector field of a vector ODE: bound variables get
their right-hand term, everything else gets derivative `0`. -/
def odeField [DecidableEq V] (sys : ODESystem V) (x : State V) : State V :=
  fun i => if i ∈ sys.bound then (sys.rhs i).eval x else 0

/-- On a well-formed system, `rhs` returns the term of *any* equation with the
given left-hand variable — the `Nodup` hypothesis makes that equation unique. -/
theorem ODESystem.rhs_eq_of_mem [DecidableEq V] {sys : ODESystem V}
    (h : sys.WellFormed) {p : V × Term V} (hp : p ∈ sys) : sys.rhs p.1 = p.2 := by
  unfold ODESystem.rhs
  cases hf : sys.find? (fun q => decide (q.1 = p.1)) with
  | none =>
      rw [List.find?_eq_none] at hf
      exact absurd (by simp : decide (p.1 = p.1) = true) (hf p hp)
  | some q =>
      have hqmem : q ∈ sys := List.mem_of_find?_eq_some hf
      have hqpred := List.find?_some hf
      have hkey : q.1 = p.1 := by simpa using hqpred
      have hqp : q = p := List.inj_on_of_nodup_map h hqmem hp hkey
      change q.2 = p.2
      rw [hqp]

variable [Fintype V] [DecidableEq V]

/-- **The bridge.** Per-component ODE semantics is equivalent to an integral curve
of the assembled field staying in the domain. -/
theorem sem_ode_iff_integralCurve {sys : ODESystem V} {ψ : Formula V}
    {ν ν' : State V} (h : sys.WellFormed) :
    Program.sem (.ode sys ψ) ν ν' ↔
      ∃ r Φ, 0 ≤ r ∧ Φ 0 = ν ∧ Φ r = ν' ∧
             IsIntegralCurveOn Φ (fun _ => odeField sys) (Set.Icc 0 r) ∧
             (∀ t ∈ Set.Icc 0 r, Formula.sat ψ (Φ t)) := by
  constructor
  · -- → assemble per-component derivatives into the integral curve
    rintro ⟨r, Φ, hr, hΦ0, hΦr, hderiv, hmask, hdom⟩
    refine ⟨r, Φ, hr, hΦ0, hΦr, ?_, hdom⟩
    change ∀ t ∈ Set.Icc 0 r, HasDerivWithinAt Φ (odeField sys (Φ t)) (Set.Icc 0 r) t
    intro t ht
    rw [hasDerivWithinAt_pi]
    intro i
    by_cases hi : i ∈ sys.bound
    · -- bound coordinate: take the equation for i
      obtain ⟨p, hp_mem, hp1⟩ := List.mem_map.mp hi
      subst hp1
      have hfield : odeField sys (Φ t) p.1 = p.2.eval (Φ t) := by
        simp only [odeField, if_pos hi, ODESystem.rhs_eq_of_mem h hp_mem]
      rw [hfield]
      exact hderiv t ht p hp_mem
    · -- non-bound coordinate: masking ⟹ constant ⟹ derivative 0
      have hfield : odeField sys (Φ t) i = 0 := by simp only [odeField, if_neg hi]
      rw [hfield]
      exact (hasDerivWithinAt_const t (Set.Icc 0 r) (ν i)).congr
        (fun y hy => hmask y hy i hi) (hmask t ht i hi)
  · -- ← recover masking from the field being 0 off the bound set
    rintro ⟨r, Φ, hr, hΦ0, hΦr, hcurve, hdom⟩
    refine ⟨r, Φ, hr, hΦ0, hΦr, ?_, ?_, hdom⟩
    · -- (a) simultaneous derivatives, per equation
      intro t ht p hp
      have hi : p.1 ∈ sys.bound := List.mem_map_of_mem hp
      have hpi := (hasDerivWithinAt_pi.mp (hcurve t ht)) p.1
      simp only [odeField, if_pos hi, ODESystem.rhs_eq_of_mem h hp] at hpi
      exact hpi
    · -- (b) masking, the careful direction
      intro t ht x hx
      -- coordinate x has within-derivative 0 on Icc (field value 0 off bound)
      have hcx : ∀ s ∈ Set.Icc (0:ℝ) r,
          HasDerivWithinAt (fun u => Φ u x) 0 (Set.Icc 0 r) s := by
        intro s hs
        have hpi := (hasDerivWithinAt_pi.mp (hcurve s hs)) x
        simpa only [odeField, if_neg hx] using hpi
      -- derivative 0 on convex Icc ⟹ constant, so Φ t x = Φ 0 x = ν x
      have hconst : ∀ s ∈ Set.Icc (0:ℝ) r, Φ s x = Φ 0 x := by
        have hdiffOn : DifferentiableOn ℝ (fun u => Φ u x) (Set.Icc 0 r) :=
          fun s hs => (hcx s hs).differentiableWithinAt
        have hd0 : ∀ s ∈ Set.Ico (0:ℝ) r,
            derivWithin (fun u => Φ u x) (Set.Icc 0 r) s = 0 := by
          intro s hs
          have hlt : (0:ℝ) < r := lt_of_le_of_lt hs.1 hs.2
          have hud : UniqueDiffWithinAt ℝ (Set.Icc 0 r) s :=
            (uniqueDiffOn_Icc hlt) s ⟨hs.1, le_of_lt hs.2⟩
          exact (hcx s ⟨hs.1, le_of_lt hs.2⟩).derivWithin hud
        exact constant_of_derivWithin_zero hdiffOn hd0
      rw [hconst t ht, hΦ0]

end DL
