/-
Copyright (c) 2026 dL-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: dL-lean contributors
-/
import DLLean.Coincidence
import DLLean.ODEBridge

/-!
# Differential invariants (DI) — semantic Lie form

No differential terms / variables. The invariant candidate `g : State V → ℝ` is a
smooth *semantic* function (Option 1: differentiability as a hypothesis; a future
syntactic-polynomial layer could discharge it). DI is a boundary/Lie invariance
theorem over `⟦{sys & ψ}⟧` (same content as relCertifier `flow_cert_sound_*`).

* `Lie` — semantic Lie derivative, `∑_{(xᵢ,θᵢ)∈sys} (∂g/∂xᵢ)·⟦θᵢ⟧`.
* `DI_strict` — `Lie < 0` on the boundary preserves `g ≤ 0`.
* `DI_nonstrict` — `Lie ≤ 0` on the boundary, sound only under a regular-boundary
  hypothesis `key`; `nonstrict_boundary_insufficient` shows why `key` is needed.

`[Fintype V]` makes `State V = V → ℝ` a finite-dimensional normed space (so `g`
has an `fderiv`); the type is unchanged.
-/

-- `[Fintype V]` is genuinely required (it supplies the normed structure on `V → ℝ`
-- via `Pi.normedAddCommGroup`), so silence the `Finite`-suggestion linter.
set_option linter.unusedFintypeInType false

namespace DL

open Set

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Semantic Lie derivative** of `g` along the field of `sys`, at `x`:
`Lie(g)(x) = ∑_{(xᵢ,θᵢ) ∈ sys} (∂g/∂xᵢ)(x) · ⟦θᵢ⟧(x)`. -/
noncomputable def Lie (sys : ODESystem V) (g : State V → ℝ) (x : State V) : ℝ :=
  (sys.map (fun p => fderiv ℝ g x (Pi.single p.1 1) * Term.eval p.2 x)).sum

/-- Semantic box over the real sublevel predicate `g ≤ 0` (the `embed`). -/
def BoxLe (α : Program V) (g : State V → ℝ) (ν : State V) : Prop :=
  ∀ ω, Program.sem α ν ω → g ω ≤ 0

/-- A continuous linear map on `V → ℝ` is the sum of its coordinate actions. -/
private theorem clm_apply_eq_sum (L : (V → ℝ) →L[ℝ] ℝ) (v : V → ℝ) :
    L v = ∑ i : V, v i * L (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have : Pi.single i (v i) = v i • Pi.single i (1 : ℝ) := by
    funext j; by_cases h : j = i <;> simp [h]
  rw [this, map_smul, smul_eq_mul]

/-- **`Lie = ∇g · field`.** The Lie sum over `sys` equals `fderiv g x` applied to
the assembled ODE field. Uses `WellFormed` (unique RHS per bound variable). -/
theorem Lie_eq_fderiv {sys : ODESystem V} {g : State V → ℝ}
    (hwf : sys.WellFormed) (x : State V) :
    fderiv ℝ g x (odeField sys x) = Lie sys g x := by
  classical
  rw [clm_apply_eq_sum]
  -- outside the bound set the field is 0, so restrict the univ-sum to bound
  have hzero : ∀ i ∈ (Finset.univ : Finset V),
      i ∉ (sys.map Prod.fst).toFinset → odeField sys x i * fderiv ℝ g x (Pi.single i 1) = 0 := by
    intro i _ hi
    have : i ∉ sys.bound := by simpa [ODESystem.bound, List.mem_toFinset] using hi
    simp [odeField, if_neg this]
  rw [← Finset.sum_subset (Finset.subset_univ _) hzero]
  -- Lie's list-sum → Finset-sum over sys.toFinset, then reindex by Prod.fst
  rw [Lie, ← List.sum_toFinset _ (hwf.of_map)]
  have himg : (sys.map Prod.fst).toFinset = sys.toFinset.image Prod.fst := by
    ext i; simp [List.mem_toFinset, List.mem_map, Finset.mem_image]
  rw [himg, Finset.sum_image (fun p hp q hq h => List.inj_on_of_nodup_map hwf
    (List.mem_toFinset.mp hp) (List.mem_toFinset.mp hq) h)]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hp' : p ∈ sys := List.mem_toFinset.mp hp
  have hpb : p.1 ∈ sys.bound := List.mem_map_of_mem hp'
  rw [odeField, if_pos hpb, ODESystem.rhs_eq_of_mem hwf hp', mul_comm]

/-- **Chain rule along the flow.** For a solution `Φ` of the ODE, `t ↦ g(Φ t)` has
within-derivative `Lie sys g (Φ t)` on `[0,r]`. -/
theorem hasDeriv_g_along_flow {sys : ODESystem V} {g : State V → ℝ}
    (hwf : sys.WellFormed) (hg : Differentiable ℝ g) {r : ℝ} {Φ : ℝ → State V}
    (hcurve : IsIntegralCurveOn Φ (fun _ => odeField sys) (Set.Icc 0 r))
    {t : ℝ} (ht : t ∈ Set.Icc 0 r) :
    HasDerivWithinAt (fun s => g (Φ s)) (Lie sys g (Φ t)) (Set.Icc 0 r) t := by
  have hchain := (hg (Φ t)).hasFDerivAt.comp_hasDerivWithinAt t (hcurve t ht)
  rw [Lie_eq_fderiv hwf] at hchain
  exact hchain

/-- **Differential invariant rule, strict form.** `g ≤ 0` initially and
`Lie(g) < 0` on the boundary `{g = 0}` within the domain ⟹ `g ≤ 0` throughout.

No `g`-scope side-condition: masking freezes non-bound coordinates, so `Lie` (the
sum over `sys`) is the complete directional derivative of `g` along the flow — a
`FV(g) ⊆ boundVars` hypothesis would be redundant and would only weaken the rule. -/
theorem DI_strict {sys : ODESystem V} {ψ : Formula V} {g : State V → ℝ}
    (hwf : sys.WellFormed) (hg : Differentiable ℝ g)
    (hbnd : ∀ x, Formula.sat ψ x → g x = 0 → Lie sys g x < 0)
    {ν : State V} (hinit : g ν ≤ 0) : BoxLe (Program.ode sys ψ) g ν := by
  intro ω hrun
  obtain ⟨r, Φ, hr, hΦ0, hΦr, hcurve, hdom⟩ := (sem_ode_iff_integralCurve hwf).mp hrun
  have hderiv : ∀ t ∈ Set.Icc (0:ℝ) r,
      HasDerivWithinAt (fun s => g (Φ s)) (Lie sys g (Φ t)) (Set.Icc 0 r) t :=
    fun t ht => hasDeriv_g_along_flow hwf hg hcurve ht
  have hcont : ContinuousOn (fun s => g (Φ s)) (Set.Icc 0 r) :=
    fun t ht => (hderiv t ht).continuousWithinAt
  rw [show ω = Φ r from hΦr.symm]
  by_contra hcon
  rw [not_le] at hcon
  -- the sublevel set the flow starts in
  set S : Set ℝ := Set.Icc 0 r ∩ (fun s => g (Φ s)) ⁻¹' Set.Iic 0 with hSdef
  have hSclosed : IsClosed S :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have h0S : (0:ℝ) ∈ S :=
    ⟨Set.left_mem_Icc.mpr hr, by simp only [Set.mem_preimage, Set.mem_Iic]; rw [hΦ0]; exact hinit⟩
  have hSbdd : BddAbove S := ⟨r, fun t ht => ht.1.2⟩
  set s := sSup S with hsdef
  have hsS : s ∈ S := hSclosed.csSup_mem ⟨0, h0S⟩ hSbdd
  have hsIcc : s ∈ Set.Icc 0 r := hsS.1
  have hsle0 : g (Φ s) ≤ 0 := hsS.2
  have hs_ub : ∀ t ∈ S, t ≤ s := fun t htS => le_csSup hSbdd htS
  clear_value s
  have hsr : s < r :=
    lt_of_le_of_ne hsIcc.2 (by rintro rfl; exact absurd hsle0 (not_le.mpr hcon))
  -- to the right of the supremum the flow has already left the sublevel set
  have hpos : ∀ t ∈ Set.Ioc s r, 0 < g (Φ t) := by
    intro t ht
    have htIcc : t ∈ Set.Icc 0 r := ⟨le_trans hsIcc.1 (le_of_lt ht.1), ht.2⟩
    have htnS : t ∉ S := fun htS => absurd (hs_ub t htS) (not_le.mpr ht.1)
    exact not_le.mp (fun h => htnS ⟨htIcc, h⟩)
  have hmem : s ∈ closure (Set.Ioc s r) := by
    rw [closure_Ioc (ne_of_lt hsr)]; exact Set.left_mem_Icc.mpr (le_of_lt hsr)
  haveI hneBot : (nhdsWithin s (Set.Ioc s r)).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hmem
  have hIocIcc : Set.Ioc s r ⊆ Set.Icc 0 r :=
    fun t ht => ⟨le_trans hsIcc.1 (le_of_lt ht.1), ht.2⟩
  -- the boundary value is exactly 0 (≤0 from S, ≥0 as a right limit)
  have hge0 : 0 ≤ g (Φ s) := by
    have htend := (hcont s hsIcc).mono_left (nhdsWithin_mono s hIocIcc)
    exact ge_of_tendsto htend
      (Filter.eventually_of_mem self_mem_nhdsWithin (fun t ht => le_of_lt (hpos t ht)))
  have hgeq0 : g (Φ s) = 0 := le_antisymm hsle0 hge0
  have hLie : Lie sys g (Φ s) < 0 := hbnd (Φ s) (hdom s hsIcc) hgeq0
  -- but the slope from the right is positive, so the derivative cannot be negative
  have hslope := (hasDerivWithinAt_iff_tendsto_slope.mp (hderiv s hsIcc)).mono_left
    (nhdsWithin_mono s (fun t ht => ⟨hIocIcc ht, ne_of_gt ht.1⟩))
  have hslopepos : ∀ᶠ t in nhdsWithin s (Set.Ioc s r),
      0 < slope (fun t => g (Φ t)) s t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [slope_def_field]
    exact div_pos (by rw [hgeq0]; simpa using hpos t ht) (by linarith [ht.1])
  exact absurd (ge_of_tendsto hslope (hslopepos.mono fun t h => le_of_lt h)) (not_le.mpr hLie)

/-- **Differential invariant rule, non-strict domain-wide form.** If `Lie(g) ≤ 0`
holds *throughout the evolution domain* (not merely on the boundary), then `g ≤ 0`
is preserved. Sound with no regularity hypothesis: `g` is non-increasing along the
flow. This is the honest, provable non-strict rule.

The tighter *boundary-only* non-strict check (`Lie ≤ 0` only on `{g = 0}`, what an
SMT solver verifies) is unsound without a regular-boundary hypothesis — see
`nonstrict_boundary_insufficient` — and a sound version needs Bony–Brezis/Nagumo
subtangency, which is not in the vendored Mathlib. -/
theorem DI_nonstrict_domain {sys : ODESystem V} {ψ : Formula V} {g : State V → ℝ}
    (hwf : sys.WellFormed) (hg : Differentiable ℝ g)
    (hbnd : ∀ x, Formula.sat ψ x → Lie sys g x ≤ 0)
    {ν : State V} (hinit : g ν ≤ 0) : BoxLe (Program.ode sys ψ) g ν := by
  intro ω hrun
  obtain ⟨r, Φ, hr, hΦ0, hΦr, hcurve, hdom⟩ := (sem_ode_iff_integralCurve hwf).mp hrun
  have hderiv : ∀ t ∈ Set.Icc (0:ℝ) r,
      HasDerivWithinAt (fun s => g (Φ s)) (Lie sys g (Φ t)) (Set.Icc 0 r) t :=
    fun t ht => hasDeriv_g_along_flow hwf hg hcurve ht
  have hcont : ContinuousOn (fun s => g (Φ s)) (Set.Icc 0 r) :=
    fun t ht => (hderiv t ht).continuousWithinAt
  have hanti : AntitoneOn (fun s => g (Φ s)) (Set.Icc 0 r) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 r) hcont (fun x hx => ?_) (fun x hx => ?_)
    · rw [interior_Icc] at hx
      have hxIcc : x ∈ Set.Icc 0 r := Set.Ioo_subset_Icc_self hx
      exact ((hderiv x hxIcc).hasDerivAt
        (Icc_mem_nhds hx.1 hx.2)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc] at hx
      have hxIcc : x ∈ Set.Icc 0 r := Set.Ioo_subset_Icc_self hx
      rw [((hderiv x hxIcc).hasDerivAt (Icc_mem_nhds hx.1 hx.2)).deriv]
      exact hbnd (Φ x) (hdom x hxIcc)
  rw [show ω = Φ r from hΦr.symm]
  calc g (Φ r) ≤ g (Φ 0) :=
        hanti (Set.left_mem_Icc.mpr hr) (Set.right_mem_Icc.mpr hr) hr
    _ = g ν := by rw [hΦ0]
    _ ≤ 0 := hinit

end DL
