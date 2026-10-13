import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux

theorem setIntegral_Ioo_comp_sub (f : ℝ → ℝ) (d : ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in Set.Ioo a b, f (d - x)) = ∫ x in Set.Ioo (d - b) (d - a), f x := by
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo (f := fun x => f (d - x)),
    ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_comp_sub_left,
    intervalIntegral.integral_of_le (sub_le_sub_left hab d),
    MeasureTheory.integral_Ioc_eq_integral_Ioo]

end Work.EllipticEst.Core.i0Aux
