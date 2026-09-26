import Mathlib
import Submission.Work.BoxShrink.Bubble.standard_counterexample

/-!
# The upper half-region of the counterexample box contains an essential loop

The companion file `standard_counterexample` shows that for the standard torus, `σ = swap 1 2`,
`c = 0`, `u = 0`, `s = 5/2`, the loop `(1,0)` is realised in `boxRegion` but in neither half-region
`upperRegion ∪ lowerRegion`.  That fact is about the *specific* winding vector `(1,0)`; it does not
say that the half-regions are inessential.

Here we show that `upperRegion` (the points of the torus inside the box with `y > 0`) *does* contain
an essential loop: the meridian circle `meridianCurve standard (π/2)`, whose winding vector is
`(0,1)`.  Indeed `σ 2 = 1`, so the cut plane is `{y = 0}` and the upper half is `{y > 0}`; the
meridian circle `{θ = π/2}` has coordinates
`(x, y, z) = (0, 2 + cos φ, sin φ)`, so `x = 0` and `y = 2 + cos φ > 0`, and its `z`- and
`y`-coordinates are automatically inside the box of size `5/2` (whose `z`- and `y`-half-widths are
`(5/2)·2^{1/3} > 1` and `(5/2)·2^{2/3} > 3`).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Bubble

noncomputable section

/-- **The upper half-region of the counterexample box contains an essential loop.**

The meridian circle `{θ = π/2}` — of winding vector `(0,1)` — lies in
`upperRegion standard (5/2) 0 (swap 1 2) 0 = F ∩ PBox (5/2) 0 (swap 1 2) ∩ {y > 0}`. -/
theorem cex_upperRegion_essential :
    Work.CoreTopology.standard.ContainsEssentialLoop
      (Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard (5 / 2) 0
        (Equiv.swap (1 : Fin 3) 2) 0) := by
  refine ⟨Work.CoreTopology.meridianCurve Work.CoreTopology.standard (Real.pi / 2),
    Work.CoreTopology.meridianCurve_essential _ _, fun t => ?_⟩
  rw [Work.BoxShrink.Core.mem_upperRegion]
  refine ⟨(Work.CoreTopology.meridianCurve Work.CoreTopology.standard (Real.pi / 2)).mem t, ?_, ?_⟩
  · -- The meridian circle lies in the box: only `|z| ≤ 1` and `|y| ≤ 3` have to be checked.
    rw [cex_mem_PBox]
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
    rw [hx, hy, hz]
    refine ⟨by norm_num, ?_, ?_⟩
    · rw [abs_lt]
      constructor
      · nlinarith [Real.neg_one_le_sin t, Submission.one_le_rpow_third]
      · nlinarith [Real.sin_le_one t, Submission.one_le_rpow_third]
    · rw [abs_lt]
      constructor
      · nlinarith [Real.neg_one_le_cos t, cex_rpow_two_thirds_gt]
      · nlinarith [Real.cos_le_one t, cex_rpow_two_thirds_gt]
  · -- `σ 2 = 1` and the `y`-coordinate is `2 + cos t > 0`.
    have h2 : (Equiv.swap (1 : Fin 3) 2) 2 = 1 := by decide
    rw [h2, Work.CoreTopology.meridianCurve_apply, Work.CoreTopology.standard_psi,
      Work.Core.torusMap_apply_one, Real.sin_pi_div_two, mul_one]
    simp
    linarith [Real.neg_one_le_cos t]

end

end Work.BoxShrink.Bubble
