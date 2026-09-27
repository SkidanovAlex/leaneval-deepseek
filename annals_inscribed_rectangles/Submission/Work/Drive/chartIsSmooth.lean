import Mathlib
import Submission.Work.Drive.sideGermDefs
import Submission.Work.Drive.planeChartDefs

/-!
# The glue between the chart lane's output and the germ route's input

The chart lane proves `∃ Q, Work.Drive.IsPlaneChart γ hγne Q`
(`Submission/Work/Drive/exists_planeChart_independent.lean`, sorry-free), while the germ route
(`Submission/Work/Drive/sideGerm.lean`) consumes

* `Work.Drive.IsSmoothChart Q` — that `Q` is a `C^∞` disk presentation of the capped plane (stated as a
  *definition* so that statements about `Q` do not have to mention the `local` charted-space instances
  of `CappingSpace`), and
* `Continuous Q` (for `Work.Drive.chartDisk_compact`, `Work.Drive.chartDisk_disjoint_nhds` and
  `Work.Drive.exists_level_lt_chartDisk`).

Both are the first conjunct of `IsPlaneChart` (its smoothness clause), transported across the two
`modelWithCornersSelf` presentations of `ℂ` and of `EuclideanSpace ℝ (Fin 4)`: `IsPlaneChart` writes
them literally as `modelWithCornersSelf ℝ ℂ` and `modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))`,
which are the same terms as `𝓘(ℝ,ℂ)` and `𝓡 4`.  This file records the transport, so that the route can
be fed from the chart lane without repeating the unfolding at each use.
-/

namespace Work.Drive

open Manifold Filter
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **A plane chart is a smooth chart** in the sense of the germ route. -/
theorem IsSmoothChart_of_isPlaneChart {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q) : IsSmoothChart Q :=
  hQ.1

/-- A plane chart is continuous (hence its disk is compact, its disjointness from its rotation is open
in the angle, and its levels are bounded below on the disk). -/
theorem continuous_of_isPlaneChart {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q) : Continuous Q :=
  (IsSmoothChart_of_isPlaneChart hQ).continuous

/-- **A plane chart is chart data for the germ route**: its smoothness clause is
`IsSmoothChart`, and its seam clause is carried along. -/
theorem IsChartData_of_isPlaneChart {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q) : IsChartData Q :=
  ⟨hQ.1, hQ.2.2.1⟩

/-- Chart data is a smooth chart. -/
theorem IsChartData.isSmoothChart {Q : ℂ → CappingSpace} (hQ : IsChartData Q) : IsSmoothChart Q :=
  hQ.1

/-- Chart data is continuous. -/
theorem IsChartData.continuous {Q : ℂ → CappingSpace} (hQ : IsChartData Q) : Continuous Q :=
  hQ.1.continuous

/-- The core loop of a chart with the seam clause is **closed** (the input `hloop` of the L6 family
engine and of `Work.Drive.eventually_ncard_meetBox_eq`). -/
theorem IsChartData.coreLoop_zero_eq_one {Q : ℂ → CappingSpace} (hQ : IsChartData Q) :
    coreLoop Q 0 = coreLoop Q 1 := by
  have h0 : Complex.exp (Real.pi * ((0 : ℝ) : ℂ) * Complex.I) = 1 := by simp
  have h1 : Complex.exp (Real.pi * ((1 : ℝ) : ℂ) * Complex.I) = (-1 : ℂ) := by
    rw [show Real.pi * ((1 : ℝ) : ℂ) * Complex.I = (Real.pi : ℂ) * Complex.I by
      push_cast; ring, Complex.exp_pi_mul_I]
  simp only [coreLoop, h0, h1]
  exact (hQ.2 1 (by simp)).symm

end

end Work.Drive
