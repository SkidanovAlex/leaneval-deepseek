import Mathlib.MeasureTheory.Integral.IntegralEqImproper

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.ModalSolution.RGW

theorem integral_deriv_eq_zero {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    (hgs : tsupport g ⊆ Set.Ioi 0) :
    ∫ x in Set.Ioi 0, deriv g x = 0 := by
  -- `g` is `C¹` with compact support, so the fundamental theorem of calculus on the half-line
  -- gives `∫_{x>0} g'(x) = -g(0)`; and `g(0) = 0` because `0` is outside the support of `g`.
  rw [hgc.integral_Ioi_deriv_eq hg 0]
  have h0 : g 0 = 0 :=
    image_eq_zero_of_notMem_tsupport fun h => absurd (hgs h) (by simp)
  simp [h0]

end Work.EllipticEst.ModalSolution.RGW
