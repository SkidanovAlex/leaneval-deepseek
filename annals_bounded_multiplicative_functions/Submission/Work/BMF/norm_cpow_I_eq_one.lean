import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

theorem norm_cpow_I_eq_one (t s : ℝ) (hs : 0 < s) :
    ‖((s:ℝ):ℂ)^(Complex.I*(t:ℂ))‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hs]
  have h : (Complex.I * (t:ℂ)).re = 0 := by simp [Complex.mul_re]
  rw [h, Real.rpow_zero]

end Work.BMF
