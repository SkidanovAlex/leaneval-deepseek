import Mathlib
import Submission.Port.Aesm

namespace Work.KMTAreas.A4

/-- Interpolation of the `ℓ^r(ℤ)` norm between `ℓ¹` and `ℓ^∞`: for a summable function `f` with
`∑' x, ‖f x‖ ≤ A` and `‖f x‖ ≤ B` for all `x`, one has `‖f‖_{ℓ^r} ≤ A^{1/r} B^{1-1/r}`
for every `r ≥ 1`.  Equivalently, `‖f‖_r ≤ ‖f‖_1^{1/r} ‖f‖_∞^{1-1/r}`, the log-convexity of the
`ℓ^p` norms. -/
theorem eLpNorm_le_of_l1_and_bounded {f : ℤ → ℂ} {A B r : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hr : 1 ≤ r) (hsum : Summable fun x : ℤ => ‖f x‖) (hle : ∑' x : ℤ, ‖f x‖ ≤ A) (hbd : ∀ x : ℤ, ‖f x‖ ≤ B) : MeasureTheory.eLpNorm f (ENNReal.ofReal r) MeasureTheory.Measure.count ≤ ENNReal.ofReal (A ^ (1 / r) * B ^ (1 - 1 / r)) := by
  have hr0 : 0 ≤ r := by linarith
  have hr1 : 0 ≤ r - 1 := by linarith
  have hnn_r : ∀ x : ℤ, 0 ≤ ‖f x‖ ^ r := fun x => Real.rpow_nonneg (norm_nonneg _) r
  -- Pointwise bound `‖f x‖^r ≤ B^{r-1} ‖f x‖`.
  have hpt : ∀ x : ℤ, ‖f x‖ ^ r ≤ B ^ (r - 1) * ‖f x‖ := by
    intro x
    have ha : 0 ≤ ‖f x‖ := norm_nonneg _
    have hsplit : ‖f x‖ ^ r = ‖f x‖ ^ (r - 1) * ‖f x‖ := by
      have h1 : r - 1 + 1 = r := by ring
      calc ‖f x‖ ^ r = ‖f x‖ ^ (r - 1 + 1) := by rw [h1]
        _ = ‖f x‖ ^ (r - 1) * ‖f x‖ ^ 1 := Real.rpow_add' ha (by linarith)
        _ = ‖f x‖ ^ (r - 1) * ‖f x‖ := by rw [Real.rpow_one]
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ha (hbd x) hr1) ha
  have hsumr : Summable fun x : ℤ => ‖f x‖ ^ r :=
    Summable.of_nonneg_of_le hnn_r hpt (Summable.mul_left (B ^ (r - 1)) hsum)
  have ht_le : (∑' x : ℤ, ‖f x‖ ^ r) ≤ A * B ^ (r - 1) := by
    calc (∑' x : ℤ, ‖f x‖ ^ r) ≤ ∑' x : ℤ, B ^ (r - 1) * ‖f x‖ :=
          Summable.tsum_le_tsum hpt hsumr (Summable.mul_left (B ^ (r - 1)) hsum)
      _ = B ^ (r - 1) * ∑' x : ℤ, ‖f x‖ := tsum_mul_left
      _ ≤ B ^ (r - 1) * A := mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hB _)
      _ = A * B ^ (r - 1) := by ring
  have ht_nonneg : 0 ≤ ∑' x : ℤ, ‖f x‖ ^ r := tsum_nonneg hnn_r
  have hexp : (r - 1) * (1 / r) = 1 - 1 / r := by
    field_simp
  -- The real inequality `(∑ ‖f x‖^r)^{1/r} ≤ A^{1/r} B^{1-1/r}`.
  have hkey : (∑' x : ℤ, ‖f x‖ ^ r) ^ (1 / r) ≤ A ^ (1 / r) * B ^ (1 - 1 / r) := by
    have h1 : (∑' x : ℤ, ‖f x‖ ^ r) ^ (1 / r) ≤ (A * B ^ (r - 1)) ^ (1 / r) :=
      Real.rpow_le_rpow ht_nonneg ht_le (by positivity)
    have h2 : (A * B ^ (r - 1)) ^ (1 / r) = A ^ (1 / r) * B ^ (1 - 1 / r) := by
      rw [Real.mul_rpow hA (Real.rpow_nonneg hB _), ← Real.rpow_mul hB (r - 1) (1 / r), hexp]
    exact h1.trans_eq h2
  have hne0 : ENNReal.ofReal r ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]; linarith
  have hnetop : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hne0 hnetop, ENNReal.toReal_ofReal hr0]
  have hlint : (∫⁻ x : ℤ, ‖f x‖ₑ ^ r ∂MeasureTheory.Measure.count) = ENNReal.ofReal (∑' x : ℤ, ‖f x‖ ^ r) := by
    rw [MeasureTheory.lintegral_count, ENNReal.ofReal_tsum_of_nonneg hnn_r hsumr]
    exact tsum_congr (fun x => by
      rw [show ‖f x‖ₑ = ENNReal.ofReal ‖f x‖ from by
        rw [enorm_eq_nnnorm, ← coe_nnnorm]
        exact ENNReal.ofReal_coe_nnreal.symm]
      exact ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr0)
  rw [hlint, ENNReal.ofReal_rpow_of_nonneg ht_nonneg (div_nonneg zero_le_one hr0)]
  exact ENNReal.ofReal_le_ofReal hkey

end Work.KMTAreas.A4
