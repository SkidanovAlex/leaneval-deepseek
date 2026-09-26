import Mathlib
import Submission.Work.BoxShrink.Bubble.standard_counterexample

/-!
# The meridian circle lies in the upper half-region for every admissible `s` and `u`

`Work.BoxShrink.Bubble.cex_upperRegion_essential` proves that the meridian circle
`meridianCurve standard (π/2)` lies in `upperRegion standard (5/2) 0 (swap 1 2) 0`.  Here we record
the two monotonicities needed to move this to the general parameter range used by the shrinking
step: enlarging the box size `s` (from `5/2` upwards) and raising the cutting height `u` (from `0`
to any `u < 1`) both keep the meridian circle inside the half-region.

Concretely, the meridian circle `{θ = π/2}` has coordinates
`(x, y, z) = (0, 2 + cos φ, sin φ)`, so it satisfies `x = 0`, `1 ≤ y ≤ 3` and `|z| ≤ 1`.  With
`σ = swap 1 2` the cut coordinate is `σ 2 = 1`, i.e. the `y`-coordinate, and

* `x = 0` lies strictly inside the `(1·s)`-half-width of the first coordinate for `s > 0`;
* `|z| ≤ 1 < 2^{1/3}·(5/2)`, so the `z`-coordinate is inside the box of size `5/2` (and hence of
  every larger size);
* `|y| = 2 + cos φ ∈ [1,3]` and `3 < (5/2)·2^{2/3}`, so the `y`-coordinate is inside the box as
  well;
* `y = 2 + cos φ ≥ 1 > u`, so the point is strictly above the cut plane.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Bubble

noncomputable section

/-- **The meridian circle `{θ = π/2}` lies in the upper half-region.**

For every box size `s ≥ 5/2`, every cutting height `u < 1` and every `t`, the point
`meridianCurve standard (π/2) t = (0, 2 + cos t, sin t)` lies in
`upperRegion standard s 0 (swap 1 2) u = F ∩ PBox s 0 (swap 1 2) ∩ {y > u}`. -/
theorem meridian_mem_upperRegion_swap (s : ℝ) (hs : 5 / 2 ≤ s) (u : ℝ) (hu : u < 1) :
    ∀ t : ℝ, (Work.CoreTopology.meridianCurve Work.CoreTopology.standard (Real.pi / 2)) t ∈
      Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard s 0
        (Equiv.swap (1 : Fin 3) 2) u := by
  intro t
  rw [Work.BoxShrink.Core.mem_upperRegion]
  refine ⟨(Work.CoreTopology.meridianCurve Work.CoreTopology.standard (Real.pi / 2)).mem t, ?_, ?_⟩
  · -- The point lies in the box of size `5/2`, hence in the box of size `s ≥ 5/2`.
    refine Submission.PBox_mono hs ?_
    have hx : (Work.CoreTopology.meridianCurve Work.CoreTopology.standard (Real.pi / 2)).γ t 0
        = 0 := by
      rw [Work.CoreTopology.meridianCurve_apply, Work.CoreTopology.standard_psi,
        Work.Core.torusMap_apply_zero, Real.cos_pi_div_two, mul_zero]
    have hy : (Work.CoreTopology.meridianCurve Work.CoreTopology.standard (Real.pi / 2)).γ t 1
        = 2 + Real.cos t := by
      rw [Work.CoreTopology.meridianCurve_apply, Work.CoreTopology.standard_psi,
        Work.Core.torusMap_apply_one, Real.sin_pi_div_two, mul_one]
    have hz : (Work.CoreTopology.meridianCurve Work.CoreTopology.standard (Real.pi / 2)).γ t 2
        = Real.sin t := by
      rw [Work.CoreTopology.meridianCurve_apply, Work.CoreTopology.standard_psi,
        Work.Core.torusMap_apply_two]
    rw [Work.BoxShrink.Bubble.cex_mem_PBox]
    refine ⟨?_, ?_, ?_⟩
    · rw [hx]; norm_num
    · rw [hz, abs_lt]
      constructor <;>
        nlinarith [Real.neg_one_le_sin t, Real.sin_le_one t, Submission.one_le_rpow_third]
    · rw [hy, abs_lt]
      constructor <;>
        nlinarith [Real.neg_one_le_cos t, Real.cos_le_one t,
          Work.BoxShrink.Bubble.cex_rpow_two_thirds_gt]
  · -- `σ 2 = 1` and the `y`-coordinate is `2 + cos t ≥ 1 > u`.
    rw [Work.BoxShrink.Bubble.cex_swap_two]
    rw [Work.CoreTopology.meridianCurve_apply, Work.CoreTopology.standard_psi,
      Work.Core.torusMap_apply_one, Real.sin_pi_div_two, mul_one]
    simp only [PiLp.zero_apply, zero_add]
    linarith [Real.neg_one_le_cos t]

end

end Work.BoxShrink.Bubble
