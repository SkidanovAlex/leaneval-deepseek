import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

lemma abel_inv_integral_cplx {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ∫ t in a..b, ((t : ℂ))⁻¹ = ((Real.log b - Real.log a : ℝ) : ℂ) := by
  have ha' : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  have hb' : (0 : ℝ) < b := lt_of_lt_of_le zero_lt_one hb
  rw [show (∫ t in a..b, ((t : ℂ))⁻¹) = ∫ t in a..b, ((t⁻¹ : ℝ) : ℂ) by
    apply intervalIntegral.integral_congr
    intro t _
    exact (Complex.ofReal_inv t).symm]
  rw [intervalIntegral.integral_ofReal, integral_inv_of_pos ha' hb']
  congr 1
  rw [Real.log_div (ne_of_gt hb') (ne_of_gt ha')]

end Work.BMF
