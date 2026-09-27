import Mathlib
import Submission.Work.Drive.germHavoidLoop
import Submission.Work.Drive.chartIsSmooth
import Submission.Work.Drive.coreLoop_disjoint_rotCapping

/-!
# The `havoid` clause of the germ route from `w ∈ Zc γ` alone

`Submission/Work/Drive/germHavoidLoop.lean` proves the `havoid` clause of the L6 family engines for the
germ route's perturbations from the **loop-vs-plane** disjointness

> `Disjoint (Set.range (coreLoop Q)) (rotCapping w '' chartDisk Q)`.

This file composes it with the chart lane's bridge
`Work.Drive.disjoint_range_coreLoop_rotCapping_chartDisk`
(`Submission/Work/Drive/coreLoop_disjoint_rotCapping.lean`), which derives that disjointness from
`w ∈ Zc γ`, the chart's `IsPlaneChart` data and the injectivity of `γ`; so the clause becomes

> **`Work.Drive.germHavoid_of_Zc`** — for a plane chart `Q` of a smooth embedded curve `γ` and an angle
> `w ∈ Zc γ`, the perturbed core loop never meets the clamped sweep of the rotated perturbed plane at a
> radial face parameter.

This is the form the germ route can *instantiate*: the disk-vs-disk hypothesis `hdisj` of
`Work.Drive.sideGerm_havoid_of_close` / `Work.Drive.sideGerm_parity_eq_of_close` is **not** a
consequence of `w ∈ Zc γ` (the `cap ∩ w·cap` piece is a genuine condition on the chart's cap), while the
loop-vs-plane form is.

**Note on axioms.**  `disjoint_range_coreLoop_rotCapping_chartDisk` is *proved* by assembling the two
halves `coreLoop_disjoint_rotCapping_stripPart` / `_capPart`, which are delegated and in flight
(`Drive/coreLoopStripDisjoint`, `Drive/coreLoopCapDisjoint`, both stated in the workspace).  So
`germHavoid_of_Zc` currently rests on `sorryAx` through those two halves; it becomes axiom-clean as soon
as they land, with no edit here.  (The companion module `germHavoidLoop.lean` is axiom-clean already.)
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

open Submission.Configuration in
/-- **The `havoid` clause of the germ route from `w ∈ Zc γ`.**  For a plane chart `Q` of an injective
nonvanishing closed curve `γ`, an angle `w ∈ Zc γ`, a chart perturbation data `Ξ`, a truncation level
`c` below the chart's levels and a base angle, there are `ε, δ > 0` such that no perturbed
configuration with `‖a‖ < ε` and `dist w' w < δ` has a meet of its core loop with the clamped sweep of
its rotated plane at a radial face parameter. -/
theorem germHavoid_of_Zc {γ : Circle → ℝ × ℝ}
    (hγne : ∀ x : Circle, γ x ≠ 0) (hγinj : Function.Injective γ)
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q)
    {m : ℕ} (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (c : ℝ) (hΞ : ChartPert Q m Ξ) (hc : 0 < c)
    (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    {w : UnitAddCircle} (hw : w ∈ Zc γ) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
      ∀ (a : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (w' : UnitAddCircle),
        ‖a‖ < ε → dist w' w < δ →
        ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
          u ∈ Submission.Drive.unitBox 1 → x ∈ Submission.Drive.unitBox 2 →
          coreLoop (pertChart Ξ Q a.1) (u 1)
            = clampedSweep c (fun t => 1 - t)
                (rotPresentation (pertChart Ξ Q a.2) w') x →
          (x 2 = 0 ∨ x 2 = 1) → False :=
  germHavoid_loop Ξ Q c hΞ (IsChartData_of_isPlaneChart hQ) hc hcbot w
    (disjoint_range_coreLoop_rotCapping_chartDisk hγne hγinj hQ hw)

end

end Work.Drive
