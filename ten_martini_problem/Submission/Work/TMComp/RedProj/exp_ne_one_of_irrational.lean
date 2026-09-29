import Mathlib

namespace Work.TMComp.RedProj

/-- If `α` is irrational and `k : ℤ` is nonzero, then `e^{2πi k α} ≠ 1`.
Indeed `exp x = 1` forces `x ∈ 2πi ℤ`, so `k α ∈ ℤ`, making `α = n / k` rational. -/
theorem exp_ne_one_of_irrational (α : ℝ) (hα : Irrational α) (k : ℤ) (hk : k ≠ 0) :
    Complex.exp (2 * Real.pi * (k : ℝ) * α * Complex.I) ≠ 1 := by
  intro h
  -- `exp x = 1` means `x` is an integer multiple of `2πi`.
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  -- the constant `2πi` is nonzero
  have hc : (2 : ℂ) * ↑Real.pi * Complex.I ≠ 0 := by
    simp [Complex.I_ne_zero, Real.pi_ne_zero]
  -- from `2πi k α = 2πi n` deduce `k α = n`
  have key : (↑k : ℂ) * ↑α = (↑n : ℂ) := by
    have h1 : (↑k : ℂ) * (↑α : ℂ) * ((2 : ℂ) * ↑Real.pi * Complex.I)
        = (↑n : ℂ) * ((2 : ℂ) * ↑Real.pi * Complex.I) := by
      rw [← hn]; push_cast; ring
    exact mul_right_cancel₀ hc h1
  have hkC : (↑k : ℂ) ≠ 0 := by exact_mod_cast hk
  -- hence `α = n / k`
  have h2 : (↑α : ℂ) = (↑n : ℂ) / (↑k : ℂ) := by
    rw [eq_div_iff hkC, mul_comm]; exact key
  -- which exhibits `α` as a rational number, contradicting irrationality
  exact hα ⟨(n : ℚ) / (k : ℚ), by
    apply Complex.ofReal_inj.mp
    rw [h2]
    push_cast
    ring⟩

end Work.TMComp.RedProj
