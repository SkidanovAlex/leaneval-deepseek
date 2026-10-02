import Mathlib
import Submission.Work.ThomBordism.sourceRegion_extChart_transition_det_pos
import Submission.Work.ThomBordism.regionPhiNeg

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The region chart is the ambient identity at interior points (site glue **G4**)

At a point `m` of the source region with `S.Φ m.1 < 0` the region chart is the ambient identity
(`Work.ThomBordism.sourceRegionMk_extChartAt_apply_of_phi_neg`).  This file records the immediate
consequences used by the site glue of `LeadChapter/ASSEMBLY.md`:

* `Work.ThomBordism.sourceRegionMk_extChartAt_symm_val` — the inverse chart sends `u` to a point whose
  ambient coordinates are `u` (for `u` in the chart target);
* `Work.ThomBordism.RegionSetupWeak.phi_neg_of_not_mem_boundary` is available from
  `Submission.Work.ThomBordism.regionPhiNeg`.

No `sorry`, no new axioms.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.ThomBordism

/-- **The inverse of the region chart at an interior point sends `u` to the point whose ambient
coordinates are `u`.** -/
theorem sourceRegionMk_extChartAt_symm_val
    {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
    {ι : Type} [Fintype ι] [Nonempty ι] {Fam : ι → Work.ThomBordism.Man8} [T2Space D.T]
    (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (mm : ℕ)
    (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ mm = 1)
    (hphi : Work.PTGeometric.SourceRegionPhiInteriorSign k
      (Work.PTGeometric.sourceZeroSet G mm hpow)
      (Work.PTGeometric.sourceBasepoint (D := D) (Fam := Fam) G mm hpow))
    (hweak : ∀ x : EuclideanHalfSpace ((8 + k) + 1),
      Work.PTGeometric.sourcePhi G mm hpow hphi x = 0 →
      mfderiv (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
        (modelWithCornersSelf ℝ ℝ) (Work.PTGeometric.sourcePhi G mm hpow hphi) x ≠ 0)
    (m : (sourceRegionMk G mm hpow hphi hweak).Region)
    (hm : (sourceRegionMk G mm hpow hphi hweak).Φ m.1 < 0) :
    ∀ u ∈ (extChartAt (𝓡∂ (8 + k + 1)) m).target,
      ((extChartAt (𝓡∂ (8 + k + 1)) m).symm u :
        (sourceRegionMk G mm hpow hphi hweak).Region).1.1 = u := by
  intro u hu
  have hmem := (extChartAt (𝓡∂ (8 + k + 1)) m).map_target hu
  rw [← sourceRegionMk_extChartAt_apply_of_phi_neg G mm hpow hphi hweak m hm _ hmem]
  exact (extChartAt (𝓡∂ (8 + k + 1)) m).right_inv hu

end Work.ThomBordism
