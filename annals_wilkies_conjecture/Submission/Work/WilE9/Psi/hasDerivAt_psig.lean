import Mathlib
import Submission.Work.WilE9.Defs

namespace Work.WilE9.Psi

/-- `psig' = -psi * psig^2`. -/
theorem hasDerivAt_psig (x : ℝ) :
    HasDerivAt Work.WilE9.psig (-(WilkiesDesign.E.psi x) * Work.WilE9.psig x ^ 2) x := by
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hne : (1 + x ^ 2 : ℝ) ≠ 0 := ne_of_gt hpos
  have hspos : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.mpr hpos
  have hsne : Real.sqrt (1 + x ^ 2) ≠ 0 := ne_of_gt hspos
  -- derivative of the inner function `y ↦ 1 + y ^ 2`
  have hinner : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
    have h := (hasDerivAt_id x).pow 2
    simpa using h.const_add 1
  -- derivative of `y ↦ √(1 + y ^ 2)`
  have hsqrt : HasDerivAt (fun y : ℝ => Real.sqrt (1 + y ^ 2))
      (x / Real.sqrt (1 + x ^ 2)) x := by
    have h := (Real.hasDerivAt_sqrt hne).comp x hinner
    have hval : (1 / (2 * Real.sqrt (1 + x ^ 2))) * (2 * x) = x / Real.sqrt (1 + x ^ 2) := by
      field_simp
    simpa only [Function.comp_apply] using hval ▸ h
  have hpsig := hsqrt.inv hsne
  -- rewrite `psig` as the pointwise inverse of `√(1 + ·²)`
  have hfun : Work.WilE9.psig = fun y : ℝ => (Real.sqrt (1 + y ^ 2))⁻¹ := by
    funext y; simp [Work.WilE9.psig, one_div]
  -- the two derivative values agree
  have hval : (-(x / Real.sqrt (1 + x ^ 2)) / (Real.sqrt (1 + x ^ 2)) ^ 2)
      = -(WilkiesDesign.E.psi x) * Work.WilE9.psig x ^ 2 := by
    rw [WilkiesDesign.E.psi, Work.WilE9.psig]
    field_simp
  rw [← hval, hfun]
  exact hpsig

end Work.WilE9.Psi
