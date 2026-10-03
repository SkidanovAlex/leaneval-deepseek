import Mathlib

-- `hℓ : 0 ≤ ℓ` is redundant (it follows from `tc ∈ Icc 0 ℓ`), but it is part of the fixed
-- statement of the theorem.
set_option linter.unusedVariables false

namespace Work.Pert.V5

/-- The elementary one-sided integral: for `y ≥ 0`, `δ > 0`,
`∫_0^y du / max δ u ≤ 1 + log (2 + y/δ)`.

On `[0, δ]` the integrand is `1/δ` (total `1`), and on `[δ, y]` it is `1/u`
(total `log (y/δ)`), which is `≤ log (2 + y/δ)`. -/
private lemma integral_inv_max_zero {δ y : ℝ} (hδ : 0 < δ) (hy : 0 ≤ y) :
    ∫ u in (0:ℝ)..y, 1 / max δ u ≤ 1 + Real.log (2 + y / δ) := by
  have hcont : Continuous fun u : ℝ => 1 / max δ u := by
    refine Continuous.div continuous_const (continuous_const.max continuous_id) ?_
    intro u
    exact ne_of_gt (lt_of_lt_of_le hδ (le_max_left δ u))
  rcases le_total y δ with hyδ | hδy
  · -- `y ≤ δ`: the integrand is constantly `1/δ` on `[0, y]`.
    have hcongr : ∫ u in (0:ℝ)..y, 1 / max δ u = ∫ u in (0:ℝ)..y, 1 / δ := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le hy] at hu
      show 1 / max δ u = 1 / δ
      rw [max_eq_left (le_trans hu.2 hyδ)]
    rw [hcongr, intervalIntegral.integral_const, smul_eq_mul]
    have hle : (y - 0) * (1 / δ) ≤ 1 := by
      rw [sub_zero, mul_one_div]
      exact (div_le_one hδ).mpr hyδ
    have hlog : (1:ℝ) ≤ 1 + Real.log (2 + y / δ) := by
      have h0 : (0:ℝ) ≤ y / δ := div_nonneg hy (le_of_lt hδ)
      have := Real.log_nonneg (show (1:ℝ) ≤ 2 + y / δ by linarith)
      linarith
    linarith
  · -- `δ ≤ y`: split at `δ`.
    have h0y : (0:ℝ) < y := lt_of_lt_of_le hδ hδy
    rw [← intervalIntegral.integral_add_adjacent_intervals
          (hcont.intervalIntegrable 0 δ) (hcont.intervalIntegrable δ y)]
    have h1 : ∫ u in (0:ℝ)..δ, 1 / max δ u = 1 := by
      have hcongr : ∫ u in (0:ℝ)..δ, 1 / max δ u = ∫ u in (0:ℝ)..δ, 1 / δ := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [Set.uIcc_of_le (le_of_lt hδ)] at hu
        show 1 / max δ u = 1 / δ
        rw [max_eq_left hu.2]
      rw [hcongr, intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_one_div,
        div_self (ne_of_gt hδ)]
    have h2 : ∫ u in δ..y, 1 / max δ u = Real.log (y / δ) := by
      have hcongr : ∫ u in δ..y, 1 / max δ u = ∫ u in δ..y, 1 / u := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [Set.uIcc_of_le hδy] at hu
        show 1 / max δ u = 1 / u
        rw [max_eq_right hu.1]
      rw [hcongr, integral_one_div_of_pos hδ h0y]
    rw [h1, h2]
    have hlog : Real.log (y / δ) ≤ Real.log (2 + y / δ) :=
      Real.log_le_log (by positivity) (by linarith)
    linarith

/-- The left half of the main estimate: for `tc ≥ 0`,
`∫_0^{tc} dt / max δ |t - tc| ≤ 1 + log (2 + tc/δ)`.  Substituting `u = tc - t` turns the
integrand `max δ |t - tc| = max δ (tc - t)` into `max δ u`. -/
private lemma integral_inv_max_left {δ tc : ℝ} (hδ : 0 < δ) (htc : 0 ≤ tc) :
    ∫ t in (0:ℝ)..tc, 1 / max δ |t - tc| ≤ 1 + Real.log (2 + tc / δ) := by
  have hcongr : ∫ t in (0:ℝ)..tc, 1 / max δ |t - tc|
      = ∫ t in (0:ℝ)..tc, 1 / max δ (tc - t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le htc] at ht
    show 1 / max δ |t - tc| = 1 / max δ (tc - t)
    rw [abs_of_nonpos (by linarith [ht.2] : t - tc ≤ 0)]
    ring_nf
  rw [hcongr, intervalIntegral.integral_comp_sub_left (fun u => 1 / max δ u) tc]
  simp only [sub_self, sub_zero]
  exact integral_inv_max_zero hδ htc

/-- The right half of the main estimate: for `tc ≤ ℓ`,
`∫_{tc}^{ℓ} dt / max δ |t - tc| ≤ 1 + log (2 + (ℓ - tc)/δ)`.  Substituting `u = t - tc` turns
the integrand into `max δ u`. -/
private lemma integral_inv_max_right {δ tc ℓ : ℝ} (hδ : 0 < δ) (htc : tc ≤ ℓ) :
    ∫ t in tc..ℓ, 1 / max δ |t - tc| ≤ 1 + Real.log (2 + (ℓ - tc) / δ) := by
  have hcongr : ∫ t in tc..ℓ, 1 / max δ |t - tc|
      = ∫ t in tc..ℓ, 1 / max δ (t + (-tc)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le htc] at ht
    show 1 / max δ |t - tc| = 1 / max δ (t + (-tc))
    rw [sub_eq_add_neg, abs_of_nonneg (by linarith [ht.1] : 0 ≤ t + (-tc))]
  rw [hcongr, intervalIntegral.integral_comp_add_right (fun u => 1 / max δ u) (-tc)]
  simp only [add_neg_cancel, sub_eq_add_neg]
  exact integral_inv_max_zero hδ (by linarith : (0:ℝ) ≤ ℓ + -tc)

/-- **Integral of `1 / max δ |t - tc|`.**  For `tc ∈ [0, ℓ]` and `δ > 0`,
`∫_0^ℓ dt / max δ |t - tc| ≤ 2 (1 + log (2 + ℓ/δ))`.
Splitting at `tc` and substituting on each half reduces this to the one-sided estimate
`∫_0^y du / max δ u ≤ 1 + log (2 + y/δ)` for `y = tc` and `y = ℓ - tc`. -/
theorem integral_inv_max_le {ℓ δ : ℝ} (hℓ : 0 ≤ ℓ) (hδ : 0 < δ) {tc : ℝ}
    (htc : tc ∈ Set.Icc (0:ℝ) ℓ) :
    ∫ t in (0:ℝ)..ℓ, 1 / max δ |t - tc| ≤ 2 * (1 + Real.log (2 + ℓ / δ)) := by
  obtain ⟨htc0, htcl⟩ := htc
  have hcont : Continuous fun t : ℝ => 1 / max δ |t - tc| := by
    refine Continuous.div continuous_const ?_ ?_
    · exact continuous_const.max (continuous_id.sub continuous_const).abs
    · intro t
      exact ne_of_gt (lt_of_lt_of_le hδ (le_max_left δ |t - tc|))
  have hL := integral_inv_max_left (δ := δ) (tc := tc) hδ htc0
  have hR := integral_inv_max_right (δ := δ) (tc := tc) (ℓ := ℓ) hδ htcl
  rw [← intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable 0 tc) (hcont.intervalIntegrable tc ℓ)]
  have hb1 : Real.log (2 + tc / δ) ≤ Real.log (2 + ℓ / δ) := by
    apply Real.log_le_log
    · have h0 : (0:ℝ) ≤ tc / δ := div_nonneg htc0 (le_of_lt hδ)
      linarith
    · have : tc / δ ≤ ℓ / δ := div_le_div_of_nonneg_right htcl (le_of_lt hδ)
      linarith
  have hb2 : Real.log (2 + (ℓ - tc) / δ) ≤ Real.log (2 + ℓ / δ) := by
    apply Real.log_le_log
    · have h0 : (0:ℝ) ≤ (ℓ - tc) / δ := div_nonneg (by linarith) (le_of_lt hδ)
      linarith
    · have : (ℓ - tc) / δ ≤ ℓ / δ := div_le_div_of_nonneg_right (by linarith) (le_of_lt hδ)
      linarith
  linarith

end Work.Pert.V5
