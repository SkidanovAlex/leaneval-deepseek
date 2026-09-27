import Mathlib
import Submission.Work.Drive.sideGermDefs
import Submission.Work.Drive.haReduction

/-!
# The level band of a chart's disk

The germ route (`Submission/Work/Drive/sideGerm.lean`) carries, besides the disjointness `hdisj` of the
two capped planes, the hypothesis

> `hcbot : ∀ p ∈ chartDisk Q, c < levelOf p`

(the truncation level `c` is *below* every level of the plane's disk), which is what excludes meets of
the core loop with the **bottom face** `x 2 = 0` of the clamped sweep — the level-`c` shadow
(`Work.Drive.clampedSweep_face_zero`).  Since `levelOf` is continuous (`Work.Drive.continuous_levelOf`)
and `chartDisk Q` is compact (`Work.Drive.chartDisk_compact`), the level function attains a minimum on
the disk, and that minimum is positive (`Work.Drive.levelOf_pos`): so some `c > 0` works.  This file
records that fact, and the companion *upper* bound (a level strictly above the whole disk), which is
what places the reference plane of the antisymmetry computation above the configuration
(`Work.Drive.exists_levelUpper_of_isPlaneChart` is the same statement for an `IsPlaneChart`; the bound
below only needs continuity of the chart).
-/

namespace Work.Drive

open Manifold Filter
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- The chart's disk is nonempty. -/
lemma chartDisk_nonempty (Q : ℂ → CappingSpace) : (chartDisk Q).Nonempty :=
  ⟨Q 0, 0, by simp [Metric.mem_closedBall], rfl⟩

/-- **A positive level strictly below the whole chart disk.**  This discharges the hypothesis `hcbot`
of `Work.Drive.sideGerm_spec` and of `Work.Drive.parityCore_of_sideGerm`: with `c` below every level of
the disk, a meet of the core loop with the bottom face `x 2 = 0` of the clamped sweep is impossible. -/
theorem exists_level_lt_chartDisk {Q : ℂ → CappingSpace} (hQ : Continuous Q) :
    ∃ c : ℝ, 0 < c ∧ ∀ p ∈ chartDisk Q, c < levelOf p := by
  obtain ⟨p₀, hp₀mem, hp₀min⟩ :=
    (chartDisk_compact hQ).exists_isMinOn (chartDisk_nonempty Q) continuous_levelOf.continuousOn
  refine ⟨levelOf p₀ / 2, by linarith [levelOf_pos p₀], fun p hp => ?_⟩
  have hle : levelOf p₀ ≤ levelOf p := hp₀min hp
  have hhalf : levelOf p₀ / 2 < levelOf p₀ := by linarith [levelOf_pos p₀]
  exact lt_of_lt_of_le hhalf hle

/-- **A level strictly above the whole chart disk** (the companion bound, for the reference plane of
the antisymmetry computation; `IsPlaneChart` is not needed, only continuity of the chart). -/
theorem exists_chartDisk_lt_level {Q : ℂ → CappingSpace} (hQ : Continuous Q) :
    ∃ β : ℝ, ∀ p ∈ chartDisk Q, levelOf p < β := by
  obtain ⟨p₀, hp₀mem, hp₀max⟩ :=
    (chartDisk_compact hQ).exists_isMaxOn (chartDisk_nonempty Q) continuous_levelOf.continuousOn
  exact ⟨levelOf p₀ + 1, fun p hp => by
    have hle : levelOf p ≤ levelOf p₀ := hp₀max hp
    linarith⟩

end

end Work.Drive
