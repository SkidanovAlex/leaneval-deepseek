import Mathlib
import Submission.Commons.Analysis.Abel.volterra_double_integral
import Submission.Commons.Analysis.Abel.hasDerivAt_invSqrt_weighted_affine

open MeasureTheory
open scoped Interval Topology

namespace Commons.Analysis.Abel

lemma intervalIntegrable_invSqrt_mul_invSqrt_sub {t x : ℝ} (htx : t < x) :
    IntervalIntegrable (fun y : ℝ => (Real.sqrt (y - t))⁻¹ * (Real.sqrt (x - y))⁻¹) volume t x := by
  let c : ℝ := x - t
  have hcpos : 0 < c := sub_pos.mpr htx
  have hcne : c ≠ 0 := ne_of_gt hcpos
  let f : ℝ → ℝ := fun u => (Real.sqrt (u * (1 - u)))⁻¹
  have hf : IntervalIntegrable f volume (0:ℝ) 1 := by
    simpa [f] using intervalIntegrable_invSqrt_weight
  -- transform (0,1) by u = (y-t)/c
  have h1 : IntervalIntegrable (fun y : ℝ => f (c⁻¹ * y)) volume (0:ℝ) c := by
    have h := hf.comp_mul_left (c := c⁻¹)
    -- h : IntervalIntegrable (fun x => f (c⁻¹ * x)) volume (0 / c⁻¹) (1 / c⁻¹)
    have h0 : (0:ℝ) / c⁻¹ = 0 := by simp
    have h1' : (1:ℝ) / c⁻¹ = c := by field_simp [hcne]
    simpa [h0, h1'] using h
  have h2 : IntervalIntegrable (fun y : ℝ => f (c⁻¹ * (y - t))) volume t x := by
    have h := h1.comp_add_right (-t)
    -- h : IntervalIntegrable (fun x => f (c⁻¹ * (x + -t))) volume (0 - -t) (c - -t)
    have hleft : (0:ℝ) - (-t) = t := by ring
    have hright : c - (-t) = x := by dsimp [c]; ring
    simpa [hleft, hright, sub_eq_add_neg] using h
  have h3 : IntervalIntegrable (fun y : ℝ => c⁻¹ * f (c⁻¹ * (y - t))) volume t x :=
    h2.const_mul c⁻¹
  have hcongr : Set.EqOn (fun y : ℝ => c⁻¹ * f (c⁻¹ * (y - t)))
      (fun y : ℝ => (Real.sqrt (y - t))⁻¹ * (Real.sqrt (x - y))⁻¹) (Set.uIoo t x) := by
    intro y hy
    have hyt' : t < y := by
      have hmin : min t x = t := min_eq_left (le_of_lt htx)
      simpa [Set.uIoo, hmin] using hy.1
    have hyx : y < x := by
      have hmax : max t x = x := max_eq_right (le_of_lt htx)
      simpa [Set.uIoo, hmax] using hy.2
    have h1 : 0 < y - t := sub_pos.mpr hyt'
    have h2 : 0 < x - y := sub_pos.mpr hyx
    have harg : c⁻¹ * (y - t) = (y - t) / c := by field_simp [hcne]
    have harg1 : 1 - (y - t) / c = (x - y) / c := by
      dsimp [c]
      field_simp [sub_ne_zero.mpr (ne_of_gt htx)]
      ring
    have hprod : ((y - t) / c) * ((x - y) / c) = ((y - t) * (x - y)) / (c * c) := by ring
    have hsqrt_prod : Real.sqrt (((y - t) / c) * ((x - y) / c)) =
        Real.sqrt ((y - t) * (x - y)) / c := by
      rw [hprod, Real.sqrt_div (mul_nonneg (le_of_lt h1) (le_of_lt h2)) (c * c)]
      have hc_sq : Real.sqrt (c * c) = c := by
        rw [Real.sqrt_mul hcpos.le c, ← sq, Real.sq_sqrt hcpos.le]
      rw [hc_sq]
    have hfval : f (c⁻¹ * (y - t)) = (Real.sqrt ((y - t) * (x - y)))⁻¹ * c := by
      dsimp [f]
      rw [harg, harg1, hsqrt_prod]
      field_simp [hcne, (Real.sqrt_pos_of_pos (mul_pos h1 h2)).ne']
    dsimp only
    rw [hfval]
    have hsqrt_mul : Real.sqrt ((y - t) * (x - y)) = Real.sqrt (y - t) * Real.sqrt (x - y) := by
      rw [Real.sqrt_mul (le_of_lt h1) (x - y)]
    rw [hsqrt_mul]
    field_simp [hcne, (Real.sqrt_pos_of_pos h1).ne', (Real.sqrt_pos_of_pos h2).ne']
  exact h3.congr_uIoo hcongr

end Commons.Analysis.Abel
