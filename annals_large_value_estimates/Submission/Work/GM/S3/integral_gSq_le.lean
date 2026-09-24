import Mathlib
import Submission.Work.GM.S3.Defs

namespace Work.GM.S3

/-- **Integral of the weight.** `∫ u, ψ₂ u * ‖Rfun W u‖² ⪯ |W|²` with a constant depending only on
`ψ₂` and `C₀`: `‖Rfun W u‖ ≤ W.card` (`Rfun_norm_le_card`) and `ψ₂` is bounded (the `j = 0` case
of `IsBumpAtOne.deriv`) and supported in `Icc (1/C₀) C₀`, an interval of length `C₀ - 1/C₀ ≤ C₀`. -/
theorem integral_gSq_le (ψ₂ : ℝ → ℝ) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) (h₂ : IsBumpAtOne ψ₂ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ W : Finset ℝ,
      ∫ u, ψ₂ u * ‖Submission.GM.Rfun W u‖ ^ 2 ≤ C * (W.card : ℝ) ^ 2 := by
  obtain ⟨_, hnonneg, hsupp, _, hderiv⟩ := h₂
  -- `ψ₂` is bounded by `c`, with `0 ≤ c` (the `j = 0` case of the derivative bounds).
  obtain ⟨c, hc, hcbd⟩ := hderiv 0
  simp only [iteratedDeriv_zero] at hcbd
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have hle : (1 : ℝ) / C₀ ≤ C₀ := by
    rw [div_le_iff₀ hC₀pos]; nlinarith
  -- the integrand is supported on the interval `Icc (1/C₀) C₀` of length `C₀ - 1/C₀ ≤ C₀`
  refine ⟨max 1 (c * C₀), lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun W => ?_⟩
  have hgint : MeasureTheory.Integrable (fun u : ℝ => c * (W.card : ℝ) ^ 2 *
      (Set.Icc (1 / C₀) C₀).indicator (fun _ => (1 : ℝ)) u) := by
    have h1 : MeasureTheory.Integrable
        ((Set.Icc (1 / C₀) C₀).indicator (fun _ : ℝ => (1 : ℝ))) := by
      rw [MeasureTheory.integrable_indicator_iff measurableSet_Icc]
      exact MeasureTheory.integrableOn_const (isCompact_Icc.measure_lt_top).ne
    exact h1.const_mul _
  have hpt : ∀ u : ℝ, ψ₂ u * ‖Submission.GM.Rfun W u‖ ^ 2 ≤
      c * (W.card : ℝ) ^ 2 * (Set.Icc (1 / C₀) C₀).indicator (fun _ => (1 : ℝ)) u := by
    intro u
    by_cases hu : u ∈ Set.Icc (1 / C₀) C₀
    · rw [Set.indicator_of_mem hu, mul_one]
      have h1 : ψ₂ u ≤ c := le_trans (le_abs_self _) (hcbd u)
      have h2 : ‖Submission.GM.Rfun W u‖ ^ 2 ≤ (W.card : ℝ) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (Rfun_norm_le_card W u) 2
      exact mul_le_mul h1 h2 (sq_nonneg _) (le_trans (hnonneg u) h1)
    · rw [Set.indicator_of_notMem hu, mul_zero]
      have hz : ψ₂ u = 0 := by
        by_contra hne
        exact hu (hsupp u hne)
      rw [hz, zero_mul]
  have hInt : ∫ u, ψ₂ u * ‖Submission.GM.Rfun W u‖ ^ 2 ≤
      ∫ u, c * (W.card : ℝ) ^ 2 * (Set.Icc (1 / C₀) C₀).indicator (fun _ => (1 : ℝ)) u :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun u => mul_nonneg (hnonneg u) (sq_nonneg _)) hgint
      (Filter.Eventually.of_forall hpt)
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.setIntegral_const, Real.volume_real_Icc_of_le hle] at hInt
  simp only [smul_eq_mul, mul_one] at hInt
  calc ∫ u, ψ₂ u * ‖Submission.GM.Rfun W u‖ ^ 2
      ≤ c * (W.card : ℝ) ^ 2 * (C₀ - 1 / C₀) := hInt
    _ ≤ max 1 (c * C₀) * (W.card : ℝ) ^ 2 := by
        have hsub : C₀ - 1 / C₀ ≤ C₀ := by
          have : (0 : ℝ) < 1 / C₀ := one_div_pos.mpr hC₀pos
          linarith
        have h3 : c * (C₀ - 1 / C₀) ≤ c * C₀ := mul_le_mul_of_nonneg_left hsub hc
        have h4 : c * (C₀ - 1 / C₀) ≤ max 1 (c * C₀) := le_trans h3 (le_max_right _ _)
        nlinarith [sq_nonneg (W.card : ℝ)]

end Work.GM.S3
