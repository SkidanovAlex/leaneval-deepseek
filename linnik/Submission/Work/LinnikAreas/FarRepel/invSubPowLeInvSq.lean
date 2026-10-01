import Mathlib

namespace Work.LinnikAreas.FarRepel

/-- **The rescaled partial-fraction weight is dominated by `A/‖u‖²` on the critical strip.** (module `Submission.Work.LinnikAreas.FarRepel.invSubPowLeInvSq`; declare in `namespace Work.LinnikAreas.FarRepel`.)

For `Re s > 1` and `k ≥ 1` there is `A > 0` with `‖(1/(s-u))^{k+1}‖ ≤ A/‖u‖²` for every `u` in the critical strip `0 < Re u < 1` with `‖u‖ ≥ 2`.  (This is exactly the hypothesis `hΦ` of `Work.LinnikAreas.FarRepel.divisorSumBallTendsto` and of `Commons.NumberTheory.DirichletCharacter.divisorSum_summable_and_tendsto` for the weight `Φ u = (1/(s-u))^{k+1}`.)

PROOF ROUTE: with `σ = Re s > 1` and `t = ‖s‖`, put `B := max 2 (2*t/(σ-1))`. Then `‖(1/(s-u))^{k+1}‖ = (1/‖s-u‖)^{k+1} ≤ B^{k+1}/‖u‖²` for `‖u‖ ≥ 1`, since `k+1 ≥ 2`: split into `2*t ≤ ‖u‖` (then `‖s-u‖ ≥ ‖u‖ - ‖s‖ ≥ ‖u‖/2`) and `2 ≤ ‖u‖ ≤ 2*t` (then `Re (s-u) = σ - Re u ≥ σ-1 > 0`, so `‖s-u‖ ≥ σ-1 ≥ ‖u‖/B`). Take `A := B^{k+1}`. Only `Mathlib` is needed. -/
theorem invSubPowLeInvSq {s : ℂ} (hs : 1 < s.re) (k : ℕ) (hk : 1 ≤ k) :
    ∃ A : ℝ, 0 < A ∧ ∀ u : ℂ, 0 < u.re → u.re < 1 → 2 ≤ ‖u‖ →
      ‖(1 / (s - u)) ^ (k + 1)‖ ≤ A / ‖u‖ ^ 2 := by
  have hσ1 : 0 < s.re - 1 := by linarith
  set B : ℝ := max 2 (2 * ‖s‖ / (s.re - 1)) with hB
  have hB2 : (2 : ℝ) ≤ B := by rw [hB]; exact le_max_left _ _
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB2
  have hB3 : 2 * ‖s‖ ≤ B * (s.re - 1) := by
    have h : 2 * ‖s‖ / (s.re - 1) ≤ B := by rw [hB]; exact le_max_right _ _
    rwa [div_le_iff₀ hσ1] at h
  refine ⟨B ^ (k + 1), pow_pos hBpos _, ?_⟩
  intro u _hu0 hu1 hu2
  have hu_pos : 0 < ‖u‖ := lt_of_lt_of_le (by norm_num) hu2
  -- Key geometric bound: ‖u‖/B ≤ ‖s - u‖
  have hkey : ‖u‖ / B ≤ ‖s - u‖ := by
    rcases le_or_gt (2 * ‖s‖) ‖u‖ with hcase | hcase
    · -- far case: ‖u‖ is large compared with ‖s‖
      have h1 : ‖u‖ ≤ ‖u - s‖ + ‖s‖ := by
        have h : u - s + s = u := sub_add_cancel u s
        calc ‖u‖ = ‖u - s + s‖ := by rw [h]
          _ ≤ ‖u - s‖ + ‖s‖ := norm_add_le _ _
      have h2 : ‖u‖ ≤ ‖s - u‖ + ‖s‖ := by
        rwa [norm_sub_rev u s] at h1
      have h5 : ‖u‖ / 2 ≤ ‖s - u‖ := by linarith
      calc ‖u‖ / B ≤ ‖u‖ / 2 := div_le_div_of_nonneg_left (norm_nonneg u) (by norm_num) hB2
        _ ≤ ‖s - u‖ := h5
    · -- close case: ‖u‖ < 2‖s‖ ≤ B(σ-1) ≤ B‖s-u‖
      have h6 : ‖u‖ / B ≤ s.re - 1 := by
        rw [div_le_iff₀ hBpos]
        have : ‖u‖ < B * (s.re - 1) := lt_of_lt_of_le hcase hB3
        nlinarith [hB3, hcase]
      have h7 : s.re - 1 ≤ ‖s - u‖ := by
        have hre : s.re - 1 ≤ (s - u).re := by
          rw [Complex.sub_re]; linarith
        exact le_trans hre (Complex.re_le_norm _)
      linarith
  have hdivpos : 0 < ‖u‖ / B := div_pos hu_pos hBpos
  have hspos : 0 < ‖s - u‖ := lt_of_lt_of_le hdivpos hkey
  have hinv : ‖s - u‖⁻¹ ≤ B / ‖u‖ := by
    have h := (inv_le_inv₀ hspos hdivpos).mpr hkey
    rwa [inv_div] at h
  have hk2 : (2 : ℕ) ≤ k + 1 := by omega
  have hu1' : (1 : ℝ) ≤ ‖u‖ := by linarith
  calc ‖(1 / (s - u)) ^ (k + 1)‖
      = (‖s - u‖⁻¹) ^ (k + 1) := by rw [norm_pow, norm_div, norm_one, one_div]
    _ ≤ (B / ‖u‖) ^ (k + 1) := pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) hinv (k + 1)
    _ = B ^ (k + 1) / ‖u‖ ^ (k + 1) := by rw [div_pow]
    _ ≤ B ^ (k + 1) / ‖u‖ ^ 2 := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact pow_le_pow_right₀ hu1' hk2

end Work.LinnikAreas.FarRepel
