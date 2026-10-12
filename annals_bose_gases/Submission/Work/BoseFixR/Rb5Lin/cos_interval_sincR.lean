import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.BoseFixR.Rb5Lin.Sinc
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.Rb5Lin

/-- The interval integral of a plane wave over `[-r, r]` is `2 r` times the cardinal sine of
`m * r` (both signs of `r` allowed; the `m = 0` and `r = 0` cases are the limiting ones). -/
theorem cos_interval_sincR (m r : ℝ) :
    (∫ s in (-r)..r, Real.cos (m * s)) = 2 * r * Work.BoseFixR.sincR (m * r) := by
  rcases eq_or_ne m 0 with hm | hm
  · subst hm
    simp only [zero_mul, Real.cos_zero]
    rw [intervalIntegral.integral_const]
    simp [Work.BoseFixR.sincR]
    ring
  · rw [intervalIntegral.integral_comp_mul_left (f := Real.cos) hm]
    rw [mul_neg, integral_cos, Real.sin_neg]
    rw [smul_eq_mul]
    rcases eq_or_ne r 0 with hr | hr
    · subst hr
      simp
    · rw [Work.BoseFixR.sincR_of_ne (mul_ne_zero hm hr)]
      field_simp
      ring

end Work.BoseFixR.Rb5Lin
