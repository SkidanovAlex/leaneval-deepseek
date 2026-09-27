import Mathlib
import Submission.Work.Drive.linPlaneTripleRange
import Submission.Work.Drive.endTripleReg_linPlaneCharts

/-!
# The all-linear row `LLL` of the ends-clause table, **unconditionally in `φ`**

This is the one-line composition that closes the last unimplemented row of
`NOTES_LEAD_hodd_blockT6.md` §3 (the `hendLLL` hypothesis of
`Work.Drive.hasClassLinearization_of_endData`) from the two bricks proved in this session:

* `Work.Drive.endTripleReg_linPlaneCharts` (`Drive/endTripleReg_linPlaneCharts`) — the assembly of the
  row from `hrank`, `hgen` and the intersection clause `hV`;
* `Work.Drive.linPlaneTripleRange` (`Drive/linPlaneTripleRange`) — the intersection clause itself, from
  `hrank` + `hgen`.

The result is the row **with no additional choice of `Φ`** beyond the general position data
`hrank`/`hgen` supplied by `Work.Drive.exists_linPlaneCharts_hgen`: in particular the `φ`-chooser of the
lead's table (needed for the *pair* row `PairReg lin₀lin₁`) is **not** needed for `LLL`.  See
`LLL_ROW_STATUS.md`.
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff

noncomputable section

/-- **The all-linear `EndTripleReg` row, unconditionally.** -/
theorem endTripleReg_linPlaneCharts_uncond
    (Φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c)
    (hrank : Module.finrank ℝ ↥(⨅ k : Fin 3, linSub (Φ k)) = 1)
    (hgen : ∀ (k : Fin 3) (z : ℂ), ‖z‖ = 1 →
      linPlaneChart (Φ k) c hc z ≠ linCommonPt Φ c hc hrank) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Eucl 3)) :=
      Work.Drive.projCharted 3
    letI : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) (Work.Drive.Ctop)
      (Projectivization ℝ (Eucl 3)) := Work.Drive.isManifold_projCharted 3
    Work.Drive.EndTripleReg
      (Work.Drive.planeClassMap (Work.Drive.diskPlane (Work.Drive.linPlaneChart (Φ 2) c hc)))
      (Work.Drive.planeClassMap (Work.Drive.diskPlane (Work.Drive.linPlaneChart (Φ 0) c hc)))
      (Work.Drive.planeClassMap (Work.Drive.diskPlane (Work.Drive.linPlaneChart (Φ 1) c hc))) :=
  Work.Drive.endTripleReg_linPlaneCharts Φ c hc hrank hgen fun y hy => by
    have key : ∀ (a b c : Submodule ℝ (EuclideanSpace ℝ (Fin 3))), a ⊓ b ⊓ c = c ⊓ a ⊓ b := by
      intro a b c
      ac_rfl
    have h := Work.Drive.linPlaneTripleRange Φ c hc hrank hgen y hy
    exact (key _ _ _).symm.trans h

end

end Work.Drive
