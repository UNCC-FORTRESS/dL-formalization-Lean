# dL-lean — status map for downstream repos

Single-program dL foundation: syntax, denotational semantics, loop metatheory, the
Mathlib-ODE bridge, a modal-axiom core, frame-aware static semantics, and
differential invariants. Apache 2.0.

**Invariant across every result:** `lake build` green, no `sorry`, and
`#print axioms` shows only `propext` / `Classical.choice` / `Quot.sound`.

## What you can import

Namespace `DL`. Variable type `V` is a parameter; `State V := V → ℝ`.

### Syntax ([Syntax.lean](DLLean/Syntax.lean))
- `Term V` = `var | const | binop AOp`; `AOp = add|sub|mul`, `CompOp` = 6 relations.
- `Program V` / `Formula V` (mutual): `assign x θ`, `assignAny x`,
  `ode (sys : ODESystem V) ψ`, `test`, `seq`, `choice`, `star`; `tt`, `cmp`, `neg`,
  `and`, `all x`, `box`.
- `ODESystem V := List (V × Term V)`; `ODESystem.WellFormed = (map Prod.fst).Nodup`
  (a variable's derivative is defined at most once). Discrete assignments are
  single-variable; only the ODE is vector-valued.

### Semantics ([Semantics.lean](DLLean/Semantics.lean))
- `Term.eval : Term V → State V → ℝ`.
- `Program.sem : Program V → State V → State V → Prop` (`⟦α⟧`).
- `Formula.sat : Formula V → State V → Prop` (`⟦ϕ⟧`); `box` is a constructor,
  `diamond`/`imp`/`or`/`ex`/`fls`/`valid` are derived.
- **ODE case:** `∃ r Φ, 0≤r ∧ Φ 0=ν ∧ Φ r=ν' ∧` (a) per-equation
  `HasDerivWithinAt (Φ·x) ⟦θ⟧ (Icc 0 r)` — conjunctive, so a malformed system is
  unsatisfiable (self-neutralizes; `WellFormed` needed only for soundness) ∧
  (b) masking: non-`sys.bound` vars constant ∧ (c) `ψ` holds throughout `[0,r]`.

### Loop ([Loop.lean](DLLean/Loop.lean))
- `sem_star : ⟦α*⟧ = ReflTransGen ⟦α⟧`.
- `sat_box_star_of_inv` : loop induction `(ϕ→[α]ϕ) ⟹ (ϕ→[α*]ϕ)`; `loop_rule`
  (valid form); `sat_box_star_iff : [α*]ϕ ↔ ϕ ∧ [α][α*]ϕ`.

### ODE bridge ([ODEBridge.lean](DLLean/ODEBridge.lean))
- `sem_ode_iff_integralCurve [Fintype V] [DecidableEq V] (h : sys.WellFormed)` :
  `⟦ode sys ψ⟧ ν ν' ↔ ∃ r Φ, … ∧ IsIntegralCurveOn Φ (fun _ => odeField sys) (Icc 0 r) ∧ …`
- `[Fintype V]` makes `State V = V → ℝ` a complete normed space **without changing
  the type**. This is the gateway to Mathlib's ODE metatheory:
  `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt` (existence),
  `ODE_solution_unique_of_mem_Icc_right` (uniqueness), and
  `dist_le_of_trajectories_ODE_of_mem` (Grönwall trajectory divergence).

### Metatheory + calculus core ([Metatheory.lean](DLLean/Metatheory.lean), [Calculus.lean](DLLean/Calculus.lean))
- `box_test`, `box_seq`, `box_choice`, `diamond_sem` (+ `@[simp]` unfold lemmas
  `sem_test/seq/choice/assign/assignAny`, `sat_box/and/neg/imp`).
- `K_axiom`, `necessitation`, `box_mono`, `sat_box_assign` (semantic `[:=]`).
- Combined, the Kleene-algebra-of-programs axioms `[?] [;] [∪] [*]` + `K` +
  necessitation + monotonicity + loop induction are all available.

### Static semantics ([Static.lean](DLLean/Static.lean), [Coincidence.lean](DLLean/Coincidence.lean))
- `Term.fv`, `Program.fv`/`Formula.fv` (mutual), `Program.bv`, `Program.mbv`.
  `FV([α]ϕ)=FV(α)∪(FV(ϕ)\MBV(α))`; `FV(α;β)` likewise; `FV(α∪β)` plain union;
  `MBV(α∪β)=MBV(α)∩MBV(β)`. ODE `BV=MBV=sys.boundSet` (LHS vars).
- `Term.coincidence`, and mutual `Formula.coincidence` / `Program.coincidence`.
  **Program coincidence is frame-aware:** given `EqOn ν ṽ V` with `V ⊇ FV(α)` and
  `(ν,ω)∈⟦α⟧`, yields `ω̃` with `(ṽ,ω̃)∈⟦α⟧` and `EqOn ω ω̃ (V ∪ MBV α)`. This
  `V∪MBV(α)` output-agreement is the reusable **frame lemma** for downstream
  freshness / non-interference side-conditions.
- `Program.bound_effect` : a run changes only `BV(α)`.
- Consumers: `V_axiom` (`FV(ϕ)∩BV(α)=∅ ⟹ ϕ→[α]ϕ`), `DW` (`[{x'=θ&ψ}]ψ`).
- Coincidence has **no `[DecidableEq V]`** in its type (classical in-proof).

### Differential invariants ([DI.lean](DLLean/DI.lean))
- `Lie sys g x = Σ_{(xᵢ,θᵢ)∈sys} fderiv ℝ g x (Pi.single xᵢ 1) · ⟦θᵢ⟧ x` — the
  semantic Lie derivative of a smooth candidate `g : State V → ℝ` along the ODE
  field. `Lie_eq_fderiv : Lie = fderiv g x (odeField sys x)` (via `WellFormed`).
- `BoxLe α g ν := ∀ ω, ⟦α⟧ ν ω → g ω ≤ 0` (the sublevel-set box).
- `DI_strict` : `g ≤ 0` initially and `Lie(g) < 0` on `{g=0}` within the domain ⟹
  `g ≤ 0` throughout. No `g`-scope side-condition needed — masking makes `Lie` the
  complete directional derivative along the flow.
- `DI_nonstrict_domain` : `Lie(g) ≤ 0` throughout the domain ⟹ invariant (sound, no
  regularity).
- `nonstrict_boundary_insufficient` : counterexample — `Lie ≤ 0` on `{g=0}` *alone*
  is unsound. A sound boundary-only form needs the closed-set flow-invariance
  (subtangency) theorem, which is not in vendored Mathlib.
- Needs `[Fintype V] [DecidableEq V]` (`fderiv` on `V → ℝ`).

## Deliberate divergences (both sound, documented in-file)
1. **No differential variables.** State is `V → ℝ`; there is no `x'` coordinate, so
   ODE `BV = MBV = sys.boundSet` (the `x`s only). Consistent with the M2 masking.
2. **Empty signature.** No uninterpreted function/predicate symbols, so the
   interpretation-agreement side-conditions are vacuous and omitted; single fixed
   interpretation.

## NOT built (out of scope — these are downstream milestones)
- **Sound boundary-only non-strict DI** — needs the closed-set flow-invariance
  (subtangency) theorem, absent from vendored Mathlib.
- **Differential ghosts** `DG` (needs Picard–Lindelöf existence — reachable from the
  ODE bridge), and the other differential axioms.
- **Uniform substitution** — no substitution operator, no contexts.
- **Relational / biprogram / ∀∃ / certificate** layers — separate downstream repos.

If you find yourself needing a substitution operator or relational modalities, you
are past this foundation's scope by design.
