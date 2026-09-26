import Mathlib

namespace Work.InnermostDisk

theorem exp_eq_exp_mul_I_exists_int {θ θ' : ℝ}
    (h : Complex.exp ((θ : ℂ) * Complex.I) = Complex.exp ((θ' : ℂ) * Complex.I)) :
    ∃ n : ℤ, θ = θ' + (n : ℝ) * (2 * Real.pi) := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  refine ⟨n, ?_⟩
  have := congrArg Complex.im hn
  simp at this
  exact this

end Work.InnermostDisk
