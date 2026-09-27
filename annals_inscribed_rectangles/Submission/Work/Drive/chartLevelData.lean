import Mathlib
import Submission.Work.Drive.planeChartDefs
import Submission.Work.Drive.sideValue
import Submission.Work.Drive.rotSweepEquivariance
import Submission.Work.Drive.hcCartesian

/-!
# The level data of a plane chart

Every brick of the chain route consumes two truncation bounds on the plane chart `Q` of
`Work.Drive.IsPlaneChart γ hγne Q`:

* `hcne` — a level `c > 0` below the chart's levels on the closed disk, and
* `hlev` — the same `c` below the levels of the *rotated presentations*
  `rotPresentation Q v` on the unit box.

Both are consequences of the chart's smoothness alone (the disk is compact and the level is strictly
positive on the capping space), but nothing in the workspace derived them from `IsPlaneChart`; they had
to be supplied by hand at every instantiation (typically through
`Work.Drive.exists_common_truncationLevel`, which asks for the *continuity* of the presentations
instead).  This file packages them, together with the continuity of the chart that they and every other
brick consume.

The second clause is free once the first is known: the rotation preserves the level
(`Work.Drive.levelOf_rotCapping`) and the rotated presentation is the rotation of the chart evaluated at
`sqDisk (foldBox y)`, a point of the closed disk (`norm_sqDisk_le_one`).
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-- **The plane chart is continuous.**  `IsPlaneChart` carries `ContMDiff` for the transparent
structure `cappingCharted` on `CappingSpace`, whose topology is the quotient topology of the capping
(the charted structure is transported along the homeomorphism `cappingSpaceHomeoProj`); hence the chart
is continuous for the topology in which `levelOf`, `diskCut` and the cuts are stated. -/
theorem continuous_of_isPlaneChart (γ : Circle → ℝ × ℝ) (hγne : ∀ x : Circle, γ x ≠ 0)
    (Q : ℂ → CappingSpace) (hQ : IsPlaneChart γ hγne Q) : Continuous Q := by
  letI := cappingCharted
  exact hQ.1.continuous

/-- **The truncation bounds of a plane chart.**  From `IsPlaneChart` alone: the chart is continuous,
there is a level `c > 0` below the chart's levels on the closed disk, and the same `c` is below the
levels of every rotated presentation on the unit box.  These are the `hcne`/`hlev` hypotheses of the
cut dichotomy and of the rigidity lemmas. -/
theorem exists_levelData_of_isPlaneChart (γ : Circle → ℝ × ℝ) (hγne : ∀ x : Circle, γ x ≠ 0)
    (Q : ℂ → CappingSpace) (hQ : IsPlaneChart γ hγne Q) :
    Continuous Q ∧ ∃ c : ℝ, 0 < c ∧ (∀ z : ℂ, ‖z‖ ≤ 1 → c ≤ levelOf (Q z)) ∧
      (∀ (v : UnitAddCircle) (y : EuclideanSpace ℝ (Fin 2)),
        y ∈ Submission.Drive.unitBox 1 → c ≤ levelOf (rotPresentation Q v y)) := by
  have hcont : Continuous Q := continuous_of_isPlaneChart γ hγne Q hQ
  refine ⟨hcont, ?_⟩
  have hcontlvl : Continuous fun x : EuclideanSpace ℝ (Fin 2) => levelOf (Q (cplxOf x)) :=
    continuous_levelOf.comp (hcont.comp continuous_cplxOf)
  obtain ⟨c, hc, hlow⟩ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1).exists_forall_le'
      hcontlvl.continuousOn (a := 0) (fun b _ => levelOf_pos (Q (cplxOf b)))
  refine ⟨c, hc, ?_, ?_⟩
  · intro z hz
    have hz' : cplxOfInv z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, ← norm_cplxOf (cplxOfInv z),
        cplxOf_cplxOfInv]
      exact hz
    simpa using hlow _ hz'
  · intro v y hy
    rw [show rotPresentation Q v y = rotCapping v (Q (sqDisk (foldBox y))) from rfl,
      levelOf_rotCapping]
    have hnorm : ‖sqDisk (foldBox y)‖ ≤ 1 := norm_sqDisk_le_one _ (foldBox_mem_unitBox y)
    have hz' : cplxOfInv (sqDisk (foldBox y)) ∈
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, ← norm_cplxOf (cplxOfInv _),
        cplxOf_cplxOfInv]
      exact hnorm
    have h := hlow (cplxOfInv (sqDisk (foldBox y))) hz'
    rwa [cplxOf_cplxOfInv] at h

end

end Work.Drive
