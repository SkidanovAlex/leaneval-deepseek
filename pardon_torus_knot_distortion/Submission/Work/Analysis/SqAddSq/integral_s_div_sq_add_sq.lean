import Mathlib

namespace Work.Analysis.SqAddSq

/-- For `A > 0` and `s > 0`, the antiderivative of `τ ↦ s / (A τ² + s²)` is
`τ ↦ (1/√A) * arctan (τ √A / s)`, whence the definite integral over `[0, ε]`. -/
theorem integral_s_div_sq_add_sq {A s ε : ℝ} (hA : 0 < A) (hs : 0 < s) (hε : 0 ≤ ε) :
    ∫ τ in (0 : ℝ)..ε, s / (A * τ ^ 2 + s ^ 2) = (1 / Real.sqrt A) * Real.arctan (ε * Real.sqrt A / s) := by
  have _hε := hε
  have hs' : s ≠ 0 := hs.ne'
  have hden : ∀ τ : ℝ, 0 < A * τ ^ 2 + s ^ 2 := by
    intro τ; nlinarith [sq_nonneg τ, sq_pos_of_pos hs, hA]
  have hderiv : ∀ τ ∈ Set.uIcc (0 : ℝ) ε,
      HasDerivAt (fun τ : ℝ => (1 / Real.sqrt A) * Real.arctan (τ * Real.sqrt A / s))
        (s / (A * τ ^ 2 + s ^ 2)) τ := by
    intro τ _
    have hg : HasDerivAt (fun τ : ℝ => τ * Real.sqrt A / s) (Real.sqrt A / s) τ := by
      simpa using ((hasDerivAt_id τ).mul_const (Real.sqrt A)).div_const s
    have hmul := hg.arctan.const_mul (1 / Real.sqrt A)
    have hd : (1 / Real.sqrt A) *
          (1 / (1 + (τ * Real.sqrt A / s) ^ 2) * (Real.sqrt A / s))
        = s / (A * τ ^ 2 + s ^ 2) := by
      have hden1 : 1 + (τ * Real.sqrt A / s) ^ 2 ≠ 0 := by positivity
      have hden2 : A * τ ^ 2 + s ^ 2 ≠ 0 := (hden τ).ne'
      field_simp
      ring_nf
      rw [Real.sq_sqrt hA.le]
    exact hmul.congr_deriv hd
  have hint : IntervalIntegrable (fun τ : ℝ => s / (A * τ ^ 2 + s ^ 2))
      MeasureTheory.volume (0 : ℝ) ε := by
    apply Continuous.intervalIntegrable
    exact continuous_const.div (by fun_prop) (fun τ => (hden τ).ne')
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp

end Work.Analysis.SqAddSq
