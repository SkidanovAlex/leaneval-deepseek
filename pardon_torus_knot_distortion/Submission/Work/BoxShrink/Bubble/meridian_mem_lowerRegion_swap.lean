import Mathlib
import Submission.Work.BoxShrink.Bubble.standard_counterexample

/-!
# The meridian circle `{θ = -π/2}` lies in the lower half-region

The sibling lemma `Work.BoxShrink.Bubble.meridian_mem_upperRegion_swap` handles the meridian
circle `{θ = π/2}`, whose coordinates are `(0, 2 + cos t, sin t)`: it lies in the *upper*
half-region for every `u < 1`.  Here we record the mirror statement: the meridian circle
`{θ = -π/2}`, whose coordinates are `(0, -(2 + cos t), sin t)`, lies in the *lower* half-region
for every `u > -1`.

The point is that the two geometric ingredients of the upper statement are insensitive to the
sign of the cut coordinate:

* the `x`-coordinate is `0`, and the other two coordinates have modulus at most `1` resp. `3`,
  so the point lies in the box of size `5/2` (`cex_boxNorm_lt_torusMap`, with
  `|x| = 0 < 5/2`), hence in the box of every larger size `s ≥ 5/2`;
* the cut coordinate is `σ 2 = 1`, i.e. the `y`-coordinate, whose value is
  `-(2 + cos t) ∈ [-3, -1]`; since `-1 < u` the point is strictly below the cut plane.
-/

namespace Work.BoxShrink.Bubble

/-- Coordinates of the meridian curve at longitude parameter `-π/2`: the first coordinate
vanishes. -/
private lemma mer_neg_pi_div_two_zero (t : ℝ) :
    (Work.CoreTopology.meridianCurve Work.CoreTopology.standard (-(Real.pi / 2))) t 0 = 0 := by
  rw [Work.CoreTopology.meridianCurve_apply, Work.CoreTopology.standard_psi,
    Work.CoreTopology.torusMap_apply_zero, Real.cos_neg, Real.cos_pi_div_two, mul_zero]

/-- Coordinates of the meridian curve at longitude parameter `-π/2`: the `y`-coordinate is
`-(2 + cos t)`. -/
private lemma mer_neg_pi_div_two_one (t : ℝ) :
    (Work.CoreTopology.meridianCurve Work.CoreTopology.standard (-(Real.pi / 2))) t 1
      = -(2 + Real.cos t) := by
  rw [Work.CoreTopology.meridianCurve_apply, Work.CoreTopology.standard_psi,
    Work.CoreTopology.torusMap_apply_one, Real.sin_neg, Real.sin_pi_div_two]
  ring

/-- Coordinates of the meridian curve at longitude parameter `-π/2`: the `z`-coordinate is
`sin t`. -/
private lemma mer_neg_pi_div_two_two (t : ℝ) :
    (Work.CoreTopology.meridianCurve Work.CoreTopology.standard (-(Real.pi / 2))) t 2
      = Real.sin t := by
  rw [Work.CoreTopology.meridianCurve_apply, Work.CoreTopology.standard_psi,
    Work.CoreTopology.torusMap_apply_two]

/-- The meridian curve at longitude parameter `-π/2` as the parametrisation. -/
private lemma mer_neg_pi_div_two_eq_torusMap (t : ℝ) :
    (Work.CoreTopology.meridianCurve Work.CoreTopology.standard (-(Real.pi / 2))) t
      = Work.Core.torusMap (-(Real.pi / 2)) t := by
  simp

/-- **The meridian circle `{θ = -π/2}` lies in the lower half-region of the box
`PBox s 0 (swap 1 2)` for every `s ≥ 5/2` and every cutting height `u > -1`.**

That is, for every `t` the point
`meridianCurve standard (-π/2) t = (0, -(2 + cos t), sin t)` lies in
`lowerRegion standard s 0 (swap 1 2) u = F ∩ PBox s 0 (swap 1 2) ∩ {y < u}`. -/
theorem meridian_mem_lowerRegion_swap (s : ℝ) (hs : 5 / 2 ≤ s) (u : ℝ) (hu : -1 < u) :
    ∀ t : ℝ, (Work.CoreTopology.meridianCurve Work.CoreTopology.standard (-(Real.pi / 2))) t ∈
      Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard s 0
        (Equiv.swap (1 : Fin 3) 2) u := by
  intro t
  rw [Work.BoxShrink.Core.mem_lowerRegion]
  refine ⟨(Work.CoreTopology.meridianCurve Work.CoreTopology.standard
    (-(Real.pi / 2))).mem t, ?_, ?_⟩
  · -- membership in the box: the box norm is `< 5/2 ≤ s`
    rw [Submission.mem_PBox_iff, mer_neg_pi_div_two_eq_torusMap]
    refine lt_of_lt_of_le ((cex_boxNorm_lt_torusMap (-(Real.pi / 2)) t).mpr ?_) hs
    rw [Work.CoreTopology.torusMap_apply_zero, Real.cos_neg, Real.cos_pi_div_two, mul_zero,
      abs_zero]
    norm_num
  · -- the cut coordinate is `y = -(2 + cos t) ≤ -1 < u`
    rw [cex_swap_two]
    rw [mer_neg_pi_div_two_one]
    simp only [PiLp.zero_apply, zero_add]
    nlinarith [Real.neg_one_le_cos t]

end Work.BoxShrink.Bubble
