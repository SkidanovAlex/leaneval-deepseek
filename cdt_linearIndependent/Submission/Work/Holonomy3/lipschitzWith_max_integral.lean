import Mathlib

namespace Work.Holonomy3

/-- For `f` continuous on `[0,1]`, the function `y ↦ ∫ u in 0..1, max y (f u)` is 1-Lipschitz
(hence continuous). Indeed `|max y c - max y' c| ≤ |y - y'|` pointwise. -/
theorem lipschitzWith_max_integral (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1)) :
    LipschitzWith 1 (fun y : ℝ => ∫ u in (0 : ℝ)..1, max y (f u)) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro y y'
  simp only [Real.dist_eq, NNReal.coe_one, one_mul]
  -- each `u ↦ max y (f u)` is continuous on `[0,1]`, hence interval integrable
  have hcont : ∀ y : ℝ, ContinuousOn (fun u => max y (f u)) (Set.uIcc (0:ℝ) 1) := by
    intro y
    have hf' : ContinuousOn f (Set.uIcc (0:ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hf
    exact ContinuousOn.sup (f := fun _ : ℝ => y) (g := f) continuousOn_const hf'
  have hint : ∀ y : ℝ, IntervalIntegrable (fun u => max y (f u)) MeasureTheory.volume (0:ℝ) 1 :=
    fun y => (hcont y).intervalIntegrable
  -- move the difference inside the integral
  have hsub : (∫ u in (0:ℝ)..1, max y (f u)) - (∫ u in (0:ℝ)..1, max y' (f u))
      = ∫ u in (0:ℝ)..1, (max y (f u) - max y' (f u)) :=
    (intervalIntegral.integral_sub (hint y) (hint y')).symm
  rw [hsub, ← Real.norm_eq_abs]
  -- the pointwise bound `|max y c - max y' c| ≤ |y - y'|` integrates to `|y - y'| · 1`
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1) (C := |y - y'|)
    (f := fun u => max y (f u) - max y' (f u)) (fun x _ => by
      rw [Real.norm_eq_abs]; exact abs_max_sub_max_le_abs y y' (f x))
  simpa using h

end Work.Holonomy3
