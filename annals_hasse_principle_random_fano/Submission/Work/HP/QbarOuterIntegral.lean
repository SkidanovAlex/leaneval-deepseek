import Mathlib

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace Work.HP

/-- `∫_{-1}^{1} |x|^n = 2/(n+1)`. -/
lemma integral_abs_pow_neg_one_one (n : ℕ) :
    (∫ x in (-1:ℝ)..1, |x| ^ n) = 2 / ((n:ℝ) + 1) := by
  have hcont : Continuous fun x : ℝ => |x| ^ n := continuous_abs.pow n
  have hsplit : (∫ x in (-1:ℝ)..1, |x| ^ n)
      = (∫ x in (-1:ℝ)..0, |x| ^ n) + (∫ x in (0:ℝ)..1, |x| ^ n) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable (-1) 0) (hcont.intervalIntegrable 0 1)).symm
  have hneg : (∫ x in (-1:ℝ)..0, |x| ^ n) = ∫ x in (0:ℝ)..1, |x| ^ n := by
    have h := intervalIntegral.integral_comp_neg (a := (-1:ℝ)) (b := 0)
      (f := fun t : ℝ => |t| ^ n)
    simpa using h
  have hone : (∫ x in (0:ℝ)..1, |x| ^ n) = ∫ x in (0:ℝ)..1, x ^ n := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    show |x| ^ n = x ^ n
    rw [abs_of_nonneg hx.1]
  rw [hsplit, hneg, hone, integral_pow, one_pow,
      zero_pow (by omega : (n + 1) ≠ 0), sub_zero]
  ring

theorem QbarOuterIntegral (d : ℕ) :
    (∫ x : ℝ, (if |x| ≤ 1 then 2 * ((d : ℝ) * |x| ^ (d + 1) + 1) / ((d : ℝ) + 1) else 0))
      = 8 / ((d : ℝ) + 2) := by
  have hiff : ∀ x : ℝ, |x| ≤ 1 ↔ x ∈ Set.Icc (-1:ℝ) 1 := by
    intro x
    rw [Set.mem_Icc, abs_le]
  have hfun : (fun x : ℝ => (if |x| ≤ 1 then 2 * ((d : ℝ) * |x| ^ (d + 1) + 1) / ((d : ℝ) + 1) else 0))
      = (Set.Icc (-1:ℝ) 1).indicator
          (fun x : ℝ => 2 * ((d : ℝ) * |x| ^ (d + 1) + 1) / ((d : ℝ) + 1)) := by
    funext x
    by_cases hx : |x| ≤ 1
    · rw [Set.indicator_of_mem ((hiff x).mp hx), ite_eq_left hx]
    · rw [Set.indicator_of_notMem (fun h => hx ((hiff x).mpr h)), ite_eq_right hx]
  rw [hfun, integral_indicator measurableSet_Icc,
      integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show (-1:ℝ) ≤ 1 by norm_num)]
  have hI1 : IntervalIntegrable (fun x : ℝ => (d:ℝ) * |x| ^ (d + 1)) volume (-1) 1 :=
    (continuous_const.mul (continuous_abs.pow (d + 1))).intervalIntegrable (-1) 1
  have hI2 : IntervalIntegrable (fun x : ℝ => (1:ℝ)) volume (-1) 1 :=
    continuous_const.intervalIntegrable (-1) 1
  have hI : (∫ x in (-1:ℝ)..1, ((d:ℝ) * |x| ^ (d + 1) + 1))
      = (d:ℝ) * (2 / ((d:ℝ) + 2)) + 2 := by
    rw [intervalIntegral.integral_add hI1 hI2, intervalIntegral.integral_const_mul,
        integral_abs_pow_neg_one_one, intervalIntegral.integral_const]
    push_cast
    rw [smul_eq_mul, mul_one]
    ring_nf
  rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, hI]
  have hD1 : (d:ℝ) + 1 ≠ 0 := by positivity
  have hD2 : (d:ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

end Work.HP
