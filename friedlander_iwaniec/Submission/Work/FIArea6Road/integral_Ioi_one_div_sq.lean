import Mathlib

namespace Work.FIArea6Road

theorem integral_Ioi_one_div_sq : ∫ s in Set.Ioi (1 : ℝ), (s ^ 2)⁻¹ = 1 := by
  have h : ∫ s in Set.Ioi (1 : ℝ), (s ^ 2)⁻¹ = ∫ s in Set.Ioi (1 : ℝ), s ^ (-2 : ℝ) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx0 : 0 ≤ x := le_of_lt (lt_trans one_pos hx)
    rw [← Real.rpow_two x, ← Real.rpow_neg hx0 2]
  rw [h, integral_Ioi_rpow_of_lt (a := -2) (c := 1) (by norm_num) (by norm_num)]
  norm_num

end Work.FIArea6Road
