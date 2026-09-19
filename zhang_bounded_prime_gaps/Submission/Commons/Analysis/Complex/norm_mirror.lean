import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.Basic
import Submission.Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic

namespace Commons.Analysis.Complex

theorem norm_mirror {a u : ℂ} {R : ℝ} (hR : 0 < R) (hu : u ≠ a) :
    ‖(a + ((R * R : ℝ) : ℂ) * ((starRingEnd ℂ) (u - a))⁻¹) - a‖ =
      (R * R : ℝ) / ‖u - a‖ := by
  have hw : u - a ≠ 0 := sub_ne_zero.mpr hu
  calc
    ‖(a + ((R * R : ℝ) : ℂ) * ((starRingEnd ℂ) (u - a))⁻¹) - a‖
        = ‖((R * R : ℝ) : ℂ) * ((starRingEnd ℂ) (u - a))⁻¹‖ := by
            rw [add_sub_cancel_left]
    _ = ‖((R * R : ℝ) : ℂ)‖ * ‖((starRingEnd ℂ) (u - a))⁻¹‖ := by
            rw [norm_mul]
    _ = (R * R) * ‖((starRingEnd ℂ) (u - a))⁻¹‖ := by
            rw [Complex.norm_of_nonneg (mul_self_nonneg R)]
    _ = (R * R) * (‖(starRingEnd ℂ) (u - a)‖)⁻¹ := by
            rw [norm_inv]
    _ = (R * R) * (‖u - a‖)⁻¹ := by
            rw [Complex.norm_conj]
    _ = (R * R) / ‖u - a‖ := by
            rw [div_eq_mul_inv]

end Commons.Analysis.Complex