import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

namespace Commons.Analysis.Integral

/-- Helper: `1 - tanh θ ^ 2 = 1 / cosh θ ^ 2`, i.e. `sech² θ = 1/cosh² θ`. -/
theorem one_sub_tanh_sq_eq_inv_cosh_sq (θ : ℝ) :
    1 - Real.tanh θ ^ 2 = 1 / Real.cosh θ ^ 2 := by
  have hc : Real.cosh θ ≠ 0 := ne_of_gt (Real.cosh_pos θ)
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  rw [Real.cosh_sq_sub_sinh_sq]

/-- Helper: the constraint `sinh θ ^ 2 = k * (θ * coth θ - 1)` forces
`sinh θ ^ 3 = k * (θ * cosh θ - sinh θ)` (multiply by `sinh θ`). -/
theorem sinh_cube_eq (θ k : ℝ) (hθ0 : 0 < θ)
    (hcon : Real.sinh θ ^ 2 = k * (θ * (Real.cosh θ / Real.sinh θ) - 1)) :
    Real.sinh θ ^ 3 = k * (θ * Real.cosh θ - Real.sinh θ) := by
  have hs : Real.sinh θ ≠ 0 := by
    intro h; have := Real.sinh_eq_zero.mp h; linarith
  have h := congrArg (· * Real.sinh θ) hcon
  rw [show (k * (θ * (Real.cosh θ / Real.sinh θ) - 1)) * Real.sinh θ
        = k * (θ * Real.cosh θ - Real.sinh θ) by field_simp] at h
  rw [show Real.sinh θ ^ 2 * Real.sinh θ = Real.sinh θ ^ 3 by ring] at h
  exact h

theorem extremal_quadratic_form_cosh {θ k : ℝ} (hθ0 : 0 < θ) (hk3 : 3 < k)
    (hcon : Real.sinh θ ^ 2 = k * (θ * (Real.cosh θ / Real.sinh θ) - 1)) :
    3 - 2 * Real.tanh θ ^ 2 + 3 * θ * Real.tanh θ - 3 * θ * (Real.cosh θ / Real.sinh θ)
      - k * (2 * (1 - Real.tanh θ ^ 2) * (1 - θ * (Real.cosh θ / Real.sinh θ)) ^ 2)
    = - (1 - Real.tanh θ ^ 2) * Real.cosh θ ^ 2
        * (3 * θ * (Real.cosh θ / Real.sinh θ) - θ * Real.tanh θ - 3) := by
  have hs : Real.sinh θ ≠ 0 := by
    intro h; have := Real.sinh_eq_zero.mp h; linarith
  have hc : Real.cosh θ ≠ 0 := ne_of_gt (Real.cosh_pos θ)
  have h3 : Real.sinh θ ^ 3 = k * (θ * Real.cosh θ - Real.sinh θ) :=
    sinh_cube_eq θ k hθ0 hcon
  rw [one_sub_tanh_sq_eq_inv_cosh_sq, Real.tanh_eq_sinh_div_cosh]
  field_simp [hs, hc]
  linear_combination (-2 * (Real.sinh θ - Real.cosh θ * θ)) * h3

end Commons.Analysis.Integral