import Mathlib

namespace Work.Asymptotics

/-- For a Möbius transformation by `γ ∈ SL(2, ℤ)` whose lower-left entry is `1`,
the action on the upper half-plane is given by `z ↦ γ₀₀ - 1/(z + γ₁₁)`. -/
theorem coe_smul_eq_of_c_eq_one {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ} (z : UpperHalfPlane)
    (hc : γ 1 0 = 1) :
    ((γ • z : UpperHalfPlane) : ℂ) = (γ 0 0 : ℂ) - 1 / ((z : ℂ) + ((γ 1 1 : ℤ) : ℂ)) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  have hdet : (γ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at hdet
  have h01 : (γ 0 1 : ℤ) = (γ 0 0 : ℤ) * (γ 1 1 : ℤ) - 1 := by
    rw [hc] at hdet; linarith
  have hden : (z : ℂ) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    exact z.im_ne_zero him
  have h00 : ((algebraMap ℤ ℝ (γ 0 0) : ℝ) : ℂ) = (γ 0 0 : ℂ) := by simp
  have h11 : ((algebraMap ℤ ℝ (γ 1 1) : ℝ) : ℂ) = (γ 1 1 : ℂ) := by simp
  have h10 : ((algebraMap ℤ ℝ (γ 1 0) : ℝ) : ℂ) = (1 : ℂ) := by simp [hc]
  have h01' : ((algebraMap ℤ ℝ (γ 0 1) : ℝ) : ℂ) = (γ 0 0 : ℂ) * (γ 1 1 : ℂ) - 1 := by
    rw [h01]; simp
  rw [h00, h01', h10, h11]
  rw [one_mul, div_eq_iff hden]
  field_simp
  ring

end Work.Asymptotics
