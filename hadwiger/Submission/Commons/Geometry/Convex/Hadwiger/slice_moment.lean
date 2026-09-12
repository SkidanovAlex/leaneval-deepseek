import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.NormNum.RealSqrt

namespace Commons.Geometry.Convex.Hadwiger

theorem slice_moment (k : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 ≤ t →
      (∫ s in (-t)..t, (Real.sqrt (t^2 - s^2))^k) = c * t^(k+1) := by
  refine ⟨∫ u in (-1)..1, (Real.sqrt (1 - u^2))^k, ?_, ?_⟩
  · apply intervalIntegral.integral_pos (show (-1:ℝ) < 1 by norm_num)
    · fun_prop
    · intro x hx
      exact pow_nonneg (Real.sqrt_nonneg _) k
    · refine ⟨0, by norm_num, ?_⟩
      norm_num
  · intro t ht
    rcases eq_or_lt_of_le ht with h | ht'
    · rw [← h]; simp
    · have key : (∫ s in (-t)..t, (Real.sqrt (t^2 - s^2))^k)
            = t^(k+1) * (∫ u in (-1)..1, (Real.sqrt (1 - u^2))^k) := by
        have hsub : (∫ s in (-t)..t, (Real.sqrt (t^2 - s^2))^k)
            = t * (∫ u in (-1)..1, (Real.sqrt (t^2 - (t*u)^2))^k) := by
          have h := intervalIntegral.smul_integral_comp_mul_left (a := -1) (b := 1)
            (fun s => (Real.sqrt (t^2 - s^2))^k) t
          simpa only [mul_neg_one, mul_one, smul_eq_mul] using h.symm
        rw [hsub]
        have hcongr : (∫ u in (-1)..1, (Real.sqrt (t^2 - (t*u)^2))^k)
            = ∫ u in (-1)..1, t^k * (Real.sqrt (1 - u^2))^k := by
          apply intervalIntegral.integral_congr
          intro u hu
          show Real.sqrt (t^2 - (t*u)^2)^k = t^k * Real.sqrt (1 - u^2)^k
          rw [Set.uIcc_of_le (show (-1:ℝ) ≤ 1 by norm_num)] at hu
          simp only [Set.mem_Icc] at hu
          have h1 : 0 ≤ u + 1 := by linarith [hu.1]
          have h2 : 0 ≤ 1 - u := by linarith [hu.2]
          have hnonneg : 0 ≤ 1 - u^2 := by nlinarith [mul_nonneg h1 h2]
          have hmul : t^2 - (t*u)^2 = t^2 * (1 - u^2) := by ring
          rw [hmul, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq (le_of_lt ht'), mul_pow]
        rw [hcongr, intervalIntegral.integral_const_mul]
        rw [pow_succ]; ring
      rw [key]; ring

end Commons.Geometry.Convex.Hadwiger