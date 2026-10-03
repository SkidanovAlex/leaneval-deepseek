import Mathlib

open MeasureTheory

namespace Work.KMTAreas.A7

/-- Comparison of the integral over a subinterval `[r₁,r₂]` of `[K,N]` with the integral over the
whole `[K,N]`, for a continuous `w : ℝ → ℂ` bounded by `B` on `[K,N]`: if `K ≤ r₁ ≤ K + q` and
`N - q < r₂ ≤ N` then the two integrals differ by at most `2 B q`. -/
theorem hull_integral_bound_c1 (w : ℝ → ℂ) (hw : Continuous w) {B : ℝ} (q : ℕ) (K N : ℕ)
    (r₁ r₂ : ℝ) (hB : ∀ t ∈ Set.Icc (K : ℝ) (N : ℝ), ‖w t‖ ≤ B)
    (hKr : (K : ℝ) ≤ r₁) (hr : r₁ ≤ r₂) (hrN : r₂ ≤ (N : ℝ))
    (hr1 : r₁ ≤ (K : ℝ) + (q : ℝ)) (hr2 : (N : ℝ) - (q : ℝ) < r₂) :
    ‖(∫ t in r₁..r₂, w t) - ∫ t in (K : ℝ)..(N : ℝ), w t‖ ≤ 2 * B * (q : ℝ) := by
  -- `[r₁,r₂]` is a subinterval of `[K,N]`, so the difference of the two integrals is the
  -- (negated) sum of the two "end pieces" `∫_K^{r₁}` and `∫_{r₂}^N`.
  have hKN : (K : ℝ) ≤ (N : ℝ) := le_trans hKr (le_trans hr hrN)
  -- `B` is nonnegative because `[K,N]` is nonempty and `w` is bounded by `B` there.
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB (K : ℝ) ⟨le_rfl, hKN⟩)
  have hint1 : IntervalIntegrable w volume (K : ℝ) r₁ := hw.intervalIntegrable _ _
  have hint2 : IntervalIntegrable w volume r₁ r₂ := hw.intervalIntegrable _ _
  have hint3 : IntervalIntegrable w volume r₂ (N : ℝ) := hw.intervalIntegrable _ _
  have h1 : (∫ t in (K : ℝ)..r₁, w t) + (∫ t in r₁..r₂, w t) = ∫ t in (K : ℝ)..r₂, w t :=
    intervalIntegral.integral_add_adjacent_intervals hint1 hint2
  have h2 : (∫ t in (K : ℝ)..r₂, w t) + (∫ t in r₂..(N : ℝ), w t)
      = ∫ t in (K : ℝ)..(N : ℝ), w t :=
    intervalIntegral.integral_add_adjacent_intervals (hint1.trans hint2) hint3
  have hsplit : (∫ t in r₁..r₂, w t) - ∫ t in (K : ℝ)..(N : ℝ), w t
      = -((∫ t in (K : ℝ)..r₁, w t) + ∫ t in r₂..(N : ℝ), w t) := by
    rw [← h2, ← h1]; ring
  -- Bound on the two end pieces.
  have hA : ‖∫ t in (K : ℝ)..r₁, w t‖ ≤ B * |r₁ - (K : ℝ)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [Set.uIoc_of_le hKr, Set.mem_Ioc] at hx
    exact hB x ⟨le_of_lt hx.1, le_trans hx.2 (le_trans hr hrN)⟩
  have hD : ‖∫ t in r₂..(N : ℝ), w t‖ ≤ B * |(N : ℝ) - r₂| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [Set.uIoc_of_le hrN, Set.mem_Ioc] at hx
    exact hB x ⟨le_trans (le_trans hKr hr) (le_of_lt hx.1), hx.2⟩
  -- The two end pieces have length at most `q`.
  have hle1 : B * |r₁ - (K : ℝ)| ≤ B * (q : ℝ) := by
    apply mul_le_mul_of_nonneg_left _ hB0
    rw [abs_of_nonneg (sub_nonneg.mpr hKr)]
    linarith
  have hle2 : B * |(N : ℝ) - r₂| ≤ B * (q : ℝ) := by
    apply mul_le_mul_of_nonneg_left _ hB0
    rw [abs_of_nonneg (sub_nonneg.mpr hrN)]
    linarith
  calc ‖(∫ t in r₁..r₂, w t) - ∫ t in (K : ℝ)..(N : ℝ), w t‖
      = ‖(∫ t in (K : ℝ)..r₁, w t) + ∫ t in r₂..(N : ℝ), w t‖ := by rw [hsplit, norm_neg]
    _ ≤ ‖∫ t in (K : ℝ)..r₁, w t‖ + ‖∫ t in r₂..(N : ℝ), w t‖ := norm_add_le _ _
    _ ≤ B * |r₁ - (K : ℝ)| + B * |(N : ℝ) - r₂| := add_le_add hA hD
    _ ≤ B * (q : ℝ) + B * (q : ℝ) := add_le_add hle1 hle2
    _ = 2 * B * (q : ℝ) := by ring

end Work.KMTAreas.A7
