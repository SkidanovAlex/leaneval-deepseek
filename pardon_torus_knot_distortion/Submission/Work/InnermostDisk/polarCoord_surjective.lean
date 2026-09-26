import Mathlib

namespace Work.InnermostDisk

theorem polarCoord_surjective (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ∃ r θ : ℝ, 0 ≤ r ∧ r ≤ 1 ∧ 0 ≤ θ ∧ θ ≤ 2 * Real.pi ∧
      (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) = z := by
  have hlo : -(Real.pi) < Complex.arg z := Complex.neg_pi_lt_arg z
  have hhi : Complex.arg z ≤ Real.pi := Complex.arg_le_pi z
  refine ⟨‖z‖, if 0 ≤ Complex.arg z then Complex.arg z else Complex.arg z + 2 * Real.pi,
    norm_nonneg z, hz, ?_, ?_, ?_⟩
  · split_ifs with h
    · exact h
    · linarith [Real.pi_pos]
  · split_ifs with h
    · linarith [Real.pi_pos]
    · linarith
  · split_ifs with h
    · exact Complex.norm_mul_exp_arg_mul_I z
    · have hper : Complex.exp (((Complex.arg z + 2 * Real.pi : ℝ) : ℂ) * Complex.I)
          = Complex.exp ((Complex.arg z : ℂ) * Complex.I) := by
        rw [show ((Complex.arg z + 2 * Real.pi : ℝ) : ℂ) * Complex.I
              = (Complex.arg z : ℂ) * Complex.I + 2 * (Real.pi : ℂ) * Complex.I by
            push_cast; ring]
        rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
      rw [hper]
      exact Complex.norm_mul_exp_arg_mul_I z

end Work.InnermostDisk
