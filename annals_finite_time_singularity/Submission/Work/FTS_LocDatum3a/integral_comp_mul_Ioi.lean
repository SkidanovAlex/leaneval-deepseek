import Mathlib.MeasureTheory.Integral.IntegralEqImproper

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_LocDatum3a

theorem integral_comp_mul_Ioi {c : ℝ} (hc : 0 < c) (R : ℝ → ℝ) :
    (∫ s in Set.Ioi 0, R (c * s) / s) = ∫ s in Set.Ioi 0, R s / s := by
  let g : ℝ → ℝ := fun t => R t / t
  have hR : (∫ s in Set.Ioi 0, R s / s) = ∫ s in Set.Ioi 0, g s := rfl
  rw [hR]
  have hpt : ∀ s : ℝ, R (c * s) / s = c • g (c * s) := by
    intro s
    show R (c * s) / s = c * (R (c * s) / (c * s))
    rw [← mul_div_assoc, mul_div_mul_left (R (c * s)) s hc.ne']
  simp_rw [hpt]
  rw [MeasureTheory.integral_smul]
  rw [MeasureTheory.integral_comp_mul_left_Ioi' g 0 hc]
  simp only [mul_zero]

end Work.FTS_LocDatum3a
