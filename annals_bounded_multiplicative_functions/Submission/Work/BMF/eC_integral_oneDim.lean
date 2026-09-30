import Mathlib
import Submission.Work.BMF.kdr_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The one-dimensional integral of the additive character `eC`

`eC t = e(t) = exp(2π i t)`.  We show that for every integer `n`,

`∫_0^1 eC (t * n) dt = 1` if `n = 0`, and `= 0` otherwise.

The integrand is written as the exponential `exp (c * t)` of a complex multiple of `t`,
so that the standard antiderivative `integral_exp_mul_complex` applies; the boundary terms
are equal because `eC` of an integer is `1`.
-/

namespace Work.BMF

open MeasureTheory

/-- The additive character, written as the exponential of a complex multiple of `t`. -/
lemma eC_mul_eq_exp (n : ℤ) (t : ℝ) :
    eC (t * (n : ℝ)) = Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) * t) := by
  unfold eC
  congr 1
  push_cast
  ring_nf

theorem eC_integral_oneDim (n : ℤ) :
    (∫ t in Set.Icc (0:ℝ) 1, Work.BMF.eC (t * (n : ℝ))) = if n = 0 then (1:ℂ) else 0 := by
  have hconv : (∫ t in Set.Icc (0:ℝ) 1, Work.BMF.eC (t * (n : ℝ)))
      = ∫ t in (0:ℝ)..1, Work.BMF.eC (t * (n:ℝ)) := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]
  rw [hconv]
  obtain hn | hn := eq_or_ne n 0
  · subst hn
    simp only [Int.cast_zero, mul_zero, ite_true]
    rw [show Work.BMF.eC 0 = 1 by simp [Work.BMF.eC], intervalIntegral.integral_const]
    norm_num
  · have hc : (2 * (Real.pi : ℂ) * Complex.I * (n:ℂ)) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
      · exact Complex.I_ne_zero
      · exact Int.cast_ne_zero.mpr hn
    have hpt : (∫ t in (0:ℝ)..1, Work.BMF.eC (t * (n:ℝ)))
        = ∫ t in (0:ℝ)..1, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (n:ℂ)) * t) := by
      apply intervalIntegral.integral_congr
      intro t _
      exact eC_mul_eq_exp n t
    have hif : (if n = 0 then (1:ℂ) else 0) = 0 := by simp [hn]
    rw [hpt, integral_exp_mul_complex hc, hif]
    have hc1 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n:ℂ)) = 1 := by
      rw [show 2 * (Real.pi:ℂ) * Complex.I * (n:ℂ) = (n:ℂ) * (2 * Real.pi * Complex.I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I n
    simp [hc1, Complex.exp_zero]

end Work.BMF
