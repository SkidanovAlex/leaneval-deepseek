import Mathlib

namespace Work.WilG4c

theorem norm_iteratedFDeriv_deriv_le (f : ℝ → ℝ) (x : ℝ) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (deriv f) x‖ = ‖iteratedFDeriv ℝ (m + 1) f x‖ := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    iteratedDeriv_succ']

end Work.WilG4c
