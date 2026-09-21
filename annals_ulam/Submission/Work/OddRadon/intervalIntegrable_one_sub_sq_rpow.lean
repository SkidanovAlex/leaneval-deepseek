import Mathlib

namespace Work.OddRadon

open MeasureTheory intervalIntegral Set

/-- The function `t ↦ (1 - t)^r` is interval integrable on `[0,1]` when `-1 < r`: it is the
composition of `x ↦ x^r` (integrable on `[0,1]` for `-1 < r`) with the reflection `t ↦ 1 - t`. -/
lemma intervalIntegrable_one_sub_pow_rpow {r : ℝ} (hr : -1 < r) :
    IntervalIntegrable (fun t : ℝ => (1 - t) ^ r) volume (0 : ℝ) 1 := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := (1 : ℝ)) hr).comp_sub_left 1
  simpa using h.symm

lemma intervalIntegrable_one_sub_sq_rpow {r : ℝ} (hr : -1 < r) :
    IntervalIntegrable (fun t : ℝ => (1 - t ^ 2) ^ r) MeasureTheory.volume (0 : ℝ) 1 := by
  have hg : IntervalIntegrable (fun t : ℝ => (1 - t) ^ r) volume (0 : ℝ) 1 :=
    intervalIntegrable_one_sub_pow_rpow hr
  have hf : ContinuousOn (fun x : ℝ => (1 + x) ^ r) (Set.uIcc (0 : ℝ) 1) := by
    refine (continuous_const.add continuous_id).continuousOn.rpow_const ?_
    intro x hx
    rw [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1), Set.mem_Icc] at hx
    exact Or.inl (ne_of_gt (show (0 : ℝ) < 1 + x by linarith [hx.1]))
  have hmul := hg.continuousOn_smul hf
  refine IntervalIntegrable.congr ?_ hmul
  intro x hx
  rw [Set.uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1), Set.mem_Ioc] at hx
  simp only [smul_eq_mul]
  rw [← Real.mul_rpow (x := 1 + x) (y := 1 - x) (z := r) (by linarith [hx.1]) (by linarith [hx.2])]
  rw [show (1 + x) * (1 - x) = 1 - x ^ 2 by ring]

end Work.OddRadon
