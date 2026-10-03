import Mathlib
import Submission.Port.Aesm

/-!
# The `ℓ^q` norm on `ℤ` with counting measure is dominated by the `ℓ²` norm, for `q ≥ 2`

For a function `f : ℤ → ℂ` and a real exponent `q ≥ 2` one has

  `eLpNorm f q Measure.count ≤ eLpNorm f 2 Measure.count`,

i.e. the `ℓ^p` norms of `f` (with respect to counting measure on `ℤ`) are non-increasing in the
exponent on `[2, ∞)`.  This is the standard monotonicity `‖f‖_q ≤ ‖f‖_p` (`p ≤ q`) valid on
measures all of whose atoms have mass at least `1`; here every point of `ℤ` has mass `1`.

The proof is a direct computation.  Writing `A = ∫⁻ n, ‖f n‖ₑ^2` and `B = ∫⁻ n, ‖f n‖ₑ^q`
(so that `eLpNorm f 2 count = A^{1/2}` and `eLpNorm f q count = B^{1/q}`), the pointwise bound

  `‖f n‖ₑ^q = ‖f n‖ₑ^{q-2} · ‖f n‖ₑ^2 ≤ A^{q/2-1} · ‖f n‖ₑ^2`

(the middle step being `‖f n‖ₑ ≤ A^{1/2}`, which follows from `‖f n‖ₑ^2 ≤ A` and is the only
place where counting measure is used: `‖f n‖ₑ^2` is one term of the series defining `A`)
sums to `B ≤ A^{q/2-1} · A`, and raising to the power `1/q` gives
`B^{1/q} ≤ A^{(q/2-1)/q + 1/q} = A^{1/2}`.  Everything is stated for `ℝ≥0∞`, so it is valid
uniformly in the degenerate cases `A = 0` and `A = ∞`.
-/

namespace Work.KMTAreas.A4

open MeasureTheory
open scoped ENNReal

/-- The `ℒᵖ` seminorm with respect to counting measure on `ℤ`, for a real exponent `p > 0`:
`eLpNorm f p count = (∫⁻ n, ‖f n‖ₑ^p)^{1/p}`. -/
theorem eLpNorm_count_ofReal_eq_rpow {f : ℤ → ℂ} {p : ℝ} (hp : 0 < p) :
    MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count
      = (∫⁻ n : ℤ, ‖f n‖ₑ ^ p ∂MeasureTheory.Measure.count) ^ (1 / p) := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (p := ENNReal.ofReal p)
    (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le]

/-- The `ℒ²` seminorm with respect to counting measure on `ℤ`:
`eLpNorm f 2 count = (∫⁻ n, ‖f n‖ₑ^2)^{1/2}`. -/
theorem eLpNorm_count_two_eq_rpow {f : ℤ → ℂ} :
    MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
      = (∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count) ^ (1 / 2 : ℝ) := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (p := 2) (by norm_num) (by norm_num),
    ENNReal.toReal_ofNat]

theorem eLpNorm_count_le_of_two_le {f : ℤ → ℂ} {q : ℝ} (hq : 2 ≤ q) : MeasureTheory.eLpNorm f (ENNReal.ofReal q) MeasureTheory.Measure.count ≤ MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
  have hq0 : (0:ℝ) < q := by linarith
  have hq0le : (0:ℝ) ≤ q := by linarith
  have hq2 : (0:ℝ) ≤ q - 2 := by linarith
  set A : ℝ≥0∞ := ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count with hA
  set B : ℝ≥0∞ := ∫⁻ n : ℤ, ‖f n‖ₑ ^ q ∂MeasureTheory.Measure.count with hB
  -- `A` is the sum of the individual `‖f n‖ₑ^2`, hence dominates each of them.
  have hAeq : A = ∑' n : ℤ, ‖f n‖ₑ ^ (2:ℝ) := by rw [hA, MeasureTheory.lintegral_count]
  -- The pointwise bound `‖f n‖ₑ^q ≤ A^{q/2-1} ‖f n‖ₑ^2`.
  have hpt : ∀ n : ℤ, ‖f n‖ₑ ^ q ≤ A ^ (q/2 - 1) * ‖f n‖ₑ ^ (2:ℝ) := by
    intro n
    have ht2le : ‖f n‖ₑ ^ (2:ℝ) ≤ A := by
      rw [hAeq]; exact ENNReal.le_tsum (f := fun n : ℤ => ‖f n‖ₑ ^ (2:ℝ)) n
    have htle : ‖f n‖ₑ ≤ A ^ (1/2 : ℝ) := by
      have h : (‖f n‖ₑ ^ (2:ℝ)) ^ (1/2 : ℝ) ≤ A ^ (1/2 : ℝ) :=
        ENNReal.rpow_le_rpow ht2le (by norm_num : (0:ℝ) ≤ 1/2)
      rwa [← ENNReal.rpow_mul, show (2:ℝ) * (1/2) = 1 by norm_num, ENNReal.rpow_one] at h
    have h1 : ‖f n‖ₑ ^ (q - 2) ≤ A ^ (q/2 - 1) := by
      have h : ‖f n‖ₑ ^ (q - 2) ≤ (A ^ (1/2 : ℝ)) ^ (q - 2) :=
        ENNReal.rpow_le_rpow htle hq2
      have h2 : (A ^ (1/2 : ℝ)) ^ (q - 2) = A ^ (q/2 - 1) := by
        rw [← ENNReal.rpow_mul]; congr 1; ring
      rwa [h2] at h
    have hsplit : ‖f n‖ₑ ^ q = ‖f n‖ₑ ^ (q - 2) * ‖f n‖ₑ ^ (2:ℝ) := by
      have h : ‖f n‖ₑ ^ ((q - 2) + 2) = ‖f n‖ₑ ^ (q - 2) * ‖f n‖ₑ ^ (2:ℝ) :=
        ENNReal.rpow_add_of_nonneg (q - 2) 2 hq2 (by norm_num : (0:ℝ) ≤ 2)
      rwa [show (q - 2) + 2 = q by ring] at h
    rw [hsplit]
    exact mul_le_mul' h1 le_rfl
  -- Summing the pointwise bound.
  have hsum_le : B ≤ A ^ (q/2 - 1) * A := by
    rw [hB, MeasureTheory.lintegral_count]
    calc ∑' n : ℤ, ‖f n‖ₑ ^ q ≤ ∑' n : ℤ, A ^ (q/2 - 1) * ‖f n‖ₑ ^ (2:ℝ) :=
          ENNReal.tsum_le_tsum hpt
      _ = A ^ (q/2 - 1) * ∑' n : ℤ, ‖f n‖ₑ ^ (2:ℝ) := ENNReal.tsum_mul_left
      _ = A ^ (q/2 - 1) * A := by rw [hAeq]
  have hfinal : B ^ (1/q) ≤ A ^ (1/2 : ℝ) := by
    have h1q : (0:ℝ) ≤ 1/q := one_div_nonneg.mpr hq0le
    have hq21 : (0:ℝ) ≤ q/2 - 1 := by linarith
    calc B ^ (1/q) ≤ (A ^ (q/2 - 1) * A) ^ (1/q) := ENNReal.rpow_le_rpow hsum_le h1q
      _ = (A ^ (q/2 - 1)) ^ (1/q) * A ^ (1/q) := ENNReal.mul_rpow_of_nonneg _ _ h1q
      _ = A ^ ((q/2 - 1) * (1/q)) * A ^ (1/q) := by rw [ENNReal.rpow_mul]
      _ = A ^ ((q/2 - 1) * (1/q) + 1/q) := by
            rw [ENNReal.rpow_add_of_nonneg ((q/2 - 1) * (1/q)) (1/q)
              (mul_nonneg hq21 h1q) h1q]
      _ = A ^ (1/2 : ℝ) := by
            congr 1
            field_simp
            ring
  rw [eLpNorm_count_ofReal_eq_rpow hq0, eLpNorm_count_two_eq_rpow]
  exact hfinal

end Work.KMTAreas.A4
