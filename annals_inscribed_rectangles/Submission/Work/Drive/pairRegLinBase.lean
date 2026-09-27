import Mathlib
import Submission.Work.Drive.linShearIncidence
import Submission.Work.Drive.pairReg_linPlaneCharts_of_incidence

/-!
# The pair row `PairReg lin₀ lin₁` of the ends clause, discharged

`Work.Drive.pairReg_linPlaneCharts_of_incidence` reduces the pair row of
`Work.Drive.hasClassLinearization_of_endData` to six linear conditions on the two charts; by
`Work.Drive.linIncidence_linBase` (`Drive/linShearIncidence.lean`) all six hold for the sheared family
`linBase A k` for **every** `A`.  Here is the resulting row, ready to instantiate at the design's
`A` (any `A`, e.g. the one produced by `Work.Drive.exists_trans_avoid_negParallel`).

This is the `hpairL0L1` hypothesis of `hasClassLinearization_of_endData`: the pair row needs **no**
`φ`-chooser — the only genuinely generic clause of the sheared linear family is the non-collision
`hgood`, which belongs to `Work.Drive.exists_linPlaneCharts_hgen`.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-- **The pair row of the sheared linear charts**: `PairReg` of the two disk charts
`planeClassMap (diskPlane (linPlaneChart (linBase A k) c hc))`, `k = 0, 1`, for every `A`. -/
theorem pairReg_linBase (A : Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c) :
    PairReg
      (planeClassMap (diskPlane (linPlaneChart (linBase A 0) c hc)))
      (planeClassMap (diskPlane (linPlaneChart (linBase A 1) c hc))) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := linIncidence_linBase A
  exact pairReg_linPlaneCharts_of_incidence (linBase A 0) (linBase A 1) c hc h1 h2 h3 h4 h5 h6


/-- **The class map of a linear disk chart does not depend on the level.** -/
theorem planeClassMap_diskPlane_linPlaneChart_eq_of_level (Φ : Eucl 3 ≃L[ℝ] Eucl 3)
    (c c' : ℝ) (hc : 0 < c) (hc' : 0 < c') :
    planeClassMap (diskPlane (linPlaneChart Φ c hc))
      = planeClassMap (diskPlane (linPlaneChart Φ c' hc')) := by
  funext y
  simp only [planeClassMap, diskPlane_apply, cappingSpaceHomeoProj_linPlaneChart]

/-- **The second pair row of the sheared linear charts** — `PairReg` of the charts `linBase A 0` and
`linBase A 2`, at *arbitrary* levels (the class map of a linear chart is level-independent,
`planeClassMap_diskPlane_linPlaneChart_eq_of_level`).  At `t = 0` the second chart is the design's
reference plane `refPlanePres φ lam hlam`, so this is the `hpairL0P2` row at the origin of the
perturbation parameter. -/
theorem pairReg_linBase_02 (A : Eucl 3 ≃L[ℝ] Eucl 3) (c lam : ℝ) (hc : 0 < c) (hlam : 0 < lam) :
    PairReg
      (planeClassMap (diskPlane (linPlaneChart (linBase A 0) c hc)))
      (planeClassMap (diskPlane (linPlaneChart (linBase A 2) lam hlam))) := by
  have h := pairReg_linPlaneCharts_of_incidence (linBase A 0) (linBase A 2) lam hlam
    (linIncidence_linBase_02 A).1 (linIncidence_linBase_02 A).2.1
    (linIncidence_linBase_02 A).2.2.1 (linIncidence_linBase_02 A).2.2.2.1
    (linIncidence_linBase_02 A).2.2.2.2.1 (linIncidence_linBase_02 A).2.2.2.2.2
  rw [← planeClassMap_diskPlane_linPlaneChart_eq_of_level (linBase A 0) c lam hc hlam] at h
  exact h

end

end Work.Drive
