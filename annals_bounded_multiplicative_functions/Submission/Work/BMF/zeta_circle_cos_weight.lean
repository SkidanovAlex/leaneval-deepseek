import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open MeasureTheory

/-- The weighted measure of the left semicircle: `∫_0^{2π} max (-cos θ) 0 dθ = 2`. -/
theorem zeta_circle_cos_weight :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), max (-(Real.cos θ)) 0) = 2 := by
  set f : ℝ → ℝ := fun θ => max (-(Real.cos θ)) 0 with hfdef
  have hcont : Continuous f := by
    rw [hfdef]; exact Real.continuous_cos.neg.max continuous_const
  have h01 : IntervalIntegrable f volume (0 : ℝ) (Real.pi / 2) := hcont.intervalIntegrable _ _
  have h12 : IntervalIntegrable f volume (Real.pi / 2) (3 * Real.pi / 2) :=
    hcont.intervalIntegrable _ _
  have h23 : IntervalIntegrable f volume (3 * Real.pi / 2) (2 * Real.pi) :=
    hcont.intervalIntegrable _ _
  have h03 : IntervalIntegrable f volume (0 : ℝ) (3 * Real.pi / 2) :=
    hcont.intervalIntegrable _ _
  have hL : (∫ θ in (0 : ℝ)..(Real.pi / 2), f θ) = 0 := by
    have hEq : Set.EqOn f (fun _ : ℝ => (0 : ℝ)) (Set.uIcc (0 : ℝ) (Real.pi / 2)) := by
      intro θ hθ
      rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] at hθ
      simp only [hfdef]
      refine le_antisymm (max_le ?_ le_rfl) (le_max_right _ _)
      exact neg_nonpos.mpr
        (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos],
          by linarith [hθ.2]⟩)
    rw [intervalIntegral.integral_congr hEq, intervalIntegral.integral_zero]
  have hM : (∫ θ in (Real.pi / 2)..(3 * Real.pi / 2), f θ) = 2 := by
    have hEq : Set.EqOn f (fun θ : ℝ => -(Real.cos θ))
        (Set.uIcc (Real.pi / 2) (3 * Real.pi / 2)) := by
      intro θ hθ
      rw [Set.uIcc_of_le (by linarith [Real.pi_pos] : Real.pi / 2 ≤ 3 * Real.pi / 2)] at hθ
      simp only [hfdef]
      refine le_antisymm (max_le le_rfl ?_) (le_max_left _ _)
      exact neg_nonneg.mpr
        (Real.cos_nonpos_of_pi_div_two_le_of_le hθ.1 (by linarith [hθ.2]))
    rw [intervalIntegral.integral_congr hEq, intervalIntegral.integral_neg, integral_cos]
    have h3 : Real.sin (3 * Real.pi / 2) = -1 := by
      have hsplit : (3 : ℝ) * Real.pi / 2 = Real.pi / 2 + Real.pi := by ring
      rw [hsplit, Real.sin_add_pi, Real.sin_pi_div_two]
    rw [h3, Real.sin_pi_div_two]
    norm_num
  have hR0 : (∫ θ in (3 * Real.pi / 2)..(2 * Real.pi), f θ) = 0 := by
    have hEq : Set.EqOn f (fun _ : ℝ => (0 : ℝ))
        (Set.uIcc (3 * Real.pi / 2) (2 * Real.pi)) := by
      intro θ hθ
      rw [Set.uIcc_of_le (by linarith [Real.pi_pos] : 3 * Real.pi / 2 ≤ 2 * Real.pi)] at hθ
      simp only [hfdef]
      refine le_antisymm (max_le ?_ le_rfl) (le_max_right _ _)
      have h2 : Real.cos θ = Real.cos (2 * Real.pi - θ) := (Real.cos_two_pi_sub θ).symm
      rw [h2]
      exact neg_nonpos.mpr (Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [hθ.2, Real.pi_pos], by linarith [hθ.1, Real.pi_pos]⟩)
    rw [intervalIntegral.integral_congr hEq, intervalIntegral.integral_zero]
  have hsplit : (∫ θ in (0 : ℝ)..(2 * Real.pi), f θ)
      = (∫ θ in (0 : ℝ)..(Real.pi / 2), f θ)
        + (∫ θ in (Real.pi / 2)..(3 * Real.pi / 2), f θ)
        + (∫ θ in (3 * Real.pi / 2)..(2 * Real.pi), f θ) := by
    have a := intervalIntegral.integral_add_adjacent_intervals h01 h12
    have b := intervalIntegral.integral_add_adjacent_intervals h03 h23
    linarith
  rw [hsplit, hL, hM, hR0]
  norm_num

end Work.BMF
