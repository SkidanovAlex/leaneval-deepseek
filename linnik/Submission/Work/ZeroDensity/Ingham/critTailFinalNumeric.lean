import Mathlib

namespace Work.ZeroDensity.Ingham

/-- For any fixed positive `C₀` and `c`, the quantity `C₀ * (5/2)^4 * exp(-(c*A))`
is eventually at most `π/10`: since `exp(-(c*A)) → 0` as `A → ∞`, one can take
`A₀` large (and at least `6`). -/
theorem critTailFinalNumeric (C₀ c : ℝ) (hC₀ : 0 < C₀) (hc : 0 < c) :
    ∃ A₀ : ℝ, 6 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
      C₀ * (5 / 2 : ℝ) ^ 4 * Real.exp (-(c * A)) ≤ Real.pi / 10 := by
  set k : ℝ := C₀ * (5 / 2 : ℝ) ^ 4 with hkdef
  have hk : 0 < k := by rw [hkdef]; positivity
  set b : ℝ := 10 * k / Real.pi with hbdef
  have hb : 0 < b := by rw [hbdef]; positivity
  refine ⟨max 6 (Real.log b / c + 1), le_max_left _ _, ?_⟩
  intro A hA
  have hA' : Real.log b / c + 1 ≤ A := le_trans (le_max_right _ _) hA
  have h1 : Real.log b / c ≤ A := by linarith
  have hlog : Real.log b ≤ c * A := by
    have := (div_le_iff₀ hc).mp h1
    rwa [mul_comm] at this
  have hexp : Real.exp (-(c * A)) ≤ b⁻¹ := by
    have h : -(c * A) ≤ -(Real.log b) := by linarith
    calc Real.exp (-(c * A)) ≤ Real.exp (-(Real.log b)) := (Real.exp_le_exp).mpr h
      _ = b⁻¹ := by rw [Real.exp_neg, Real.exp_log hb]
  calc C₀ * (5 / 2 : ℝ) ^ 4 * Real.exp (-(c * A)) = k * Real.exp (-(c * A)) := by rw [hkdef]
    _ ≤ k * b⁻¹ := by
        apply mul_le_mul_of_nonneg_left hexp (le_of_lt hk)
    _ = Real.pi / 10 := by rw [hbdef]; field_simp

end Work.ZeroDensity.Ingham
