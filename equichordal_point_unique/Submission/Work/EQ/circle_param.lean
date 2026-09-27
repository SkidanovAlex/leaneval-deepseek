import Mathlib

namespace Work.EQ

theorem circle_param (c : ℂ) (hc : ‖c‖ = 1) :
    (∀ θ : ℝ, ‖Complex.exp ((θ : ℂ) * Complex.I) * c‖ = 1) ∧
    (∀ θ : ℝ, Complex.exp (((θ + Real.pi) : ℂ) * Complex.I) * c
        = -(Complex.exp ((θ : ℂ) * Complex.I) * c)) ∧
    (∀ z : ℂ, ‖z‖ = 1 → ∃ θ : ℝ, Complex.exp ((θ : ℂ) * Complex.I) * c = z) := by
  refine ⟨?_, ?_, ?_⟩
  · intro θ
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, hc, mul_one]
  · intro θ
    rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  · intro z hz
    have hcne : c ≠ 0 := by
      intro h; rw [h, norm_zero] at hc; exact one_ne_zero hc.symm
    obtain ⟨θ, hθ⟩ :=
      (Complex.norm_eq_one_iff (z := z / c)).mp (by rw [norm_div, hz, hc, div_one])
    exact ⟨θ, by rw [hθ, div_mul_cancel₀ z hcne]⟩

end Work.EQ
