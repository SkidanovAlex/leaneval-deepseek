import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol

/-- Change of variables `θ = π/2 - φ` (the reflection about `π/4`) on the two halves of `(0, π/2)`:
the integral over `(π/4, π/2)` equals the integral over `(0, π/4)` of the reflected integrand. -/
theorem mirrorIooIntegral (F : ℝ → ℝ)
    (hF : MeasureTheory.IntegrableOn F (Set.Ioo (Real.pi / 4) (Real.pi / 2))) :
    (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), F θ)
      = ∫ φ in Set.Ioo 0 (Real.pi / 4), F (Real.pi / 2 - φ) := by
  have _hF := hF
  have hle : (0 : ℝ) ≤ Real.pi / 4 := by linarith [Real.pi_pos]
  have hle2 : Real.pi / 4 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hL : (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), F θ)
      = ∫ θ in (Real.pi / 4)..(Real.pi / 2), F θ := by
    rw [intervalIntegral.integral_of_le hle2, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  have hR : (∫ φ in Set.Ioo 0 (Real.pi / 4), F (Real.pi / 2 - φ))
      = ∫ φ in (0 : ℝ)..(Real.pi / 4), F (Real.pi / 2 - φ) := by
    rw [intervalIntegral.integral_of_le hle, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [hL, hR, intervalIntegral.integral_comp_sub_left F (Real.pi / 2)]
  norm_num [show Real.pi / 2 - Real.pi / 4 = Real.pi / 4 by ring,
            show Real.pi / 2 - 0 = Real.pi / 2 by ring]

end Work.FTS.EllSol
