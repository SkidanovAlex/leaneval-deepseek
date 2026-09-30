import Mathlib
import Submission.Work.BMF.TentDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- For `r ≠ 0` the `r`-th Fourier coefficient of the tent of width `B` is bounded by
`(1/(π² B)) · 1/r²`. -/
lemma tentCoeff_abs_le {B : ℝ} (hB : 0 < B) (r : ℤ) (hr : r ≠ 0) :
    |tentCoeff B r| ≤ (1 / (Real.pi ^ 2 * B)) * (1 / (r : ℝ) ^ 2) := by
  have hden : 0 < (Real.pi ^ 2 * (r : ℝ) ^ 2 * B) := by
    have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr
    positivity
  have hval : tentCoeff B r
      = Real.sin (Real.pi * (r : ℝ) * B) ^ 2 / (Real.pi ^ 2 * (r : ℝ) ^ 2 * B) := by
    simp [tentCoeff, hr]
  rw [hval, abs_of_nonneg (by positivity)]
  calc Real.sin (Real.pi * ↑r * B) ^ 2 / (Real.pi ^ 2 * ↑r ^ 2 * B)
      ≤ 1 / (Real.pi ^ 2 * ↑r ^ 2 * B) :=
        div_le_div_of_nonneg_right (Real.sin_sq_le_one _) hden.le
    _ = (1 / (Real.pi ^ 2 * B)) * (1 / (↑r) ^ 2) := by field_simp

/-- The Fourier coefficients of the tent of width `B > 0` are summable: they are dominated by
a constant multiple of `1/r²`, which is a convergent `p`-series over `ℤ`. -/
theorem tentCoeff_summable {B : ℝ} (hB : 0 < B) : Summable (tentCoeff B) := by
  have hbound : ∀ r : ℤ, r ≠ 0 →
      ‖tentCoeff B r‖ ≤ (1 / (Real.pi ^ 2 * B)) * (1 / (r : ℝ) ^ 2) :=
    fun r hr => by rw [Real.norm_eq_abs]; exact tentCoeff_abs_le hB r hr
  refine Summable.of_norm_bounded_eventually
    (g := fun r : ℤ => (1 / (Real.pi ^ 2 * B)) * (1 / (r : ℝ) ^ 2)) ?_ ?_
  · exact ((Real.summable_one_div_int_pow (p := 2)).mpr (by norm_num)).mul_left
      (1 / (Real.pi ^ 2 * B))
  · filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with r hr
    exact hbound r hr

end Work.BMF
