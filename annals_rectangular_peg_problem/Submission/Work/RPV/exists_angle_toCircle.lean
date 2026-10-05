import Mathlib

namespace Work.RPV

theorem exists_angle_toCircle (c : ℂ) (hc : ‖c‖ = 1) :
    ∃ θ : Real.Angle, (θ.toCircle : ℂ) = c := by
  refine ⟨(Complex.arg c : Real.Angle), ?_⟩
  rw [Real.Angle.toCircle_coe, Circle.coe_exp]
  have h := Complex.norm_mul_exp_arg_mul_I c
  rw [hc] at h
  simpa using h

end Work.RPV
