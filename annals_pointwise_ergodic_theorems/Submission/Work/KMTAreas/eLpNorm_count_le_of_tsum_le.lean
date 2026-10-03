import Mathlib
import Submission.Port.Aesm

namespace Work.KMTAreas

open MeasureTheory ENNReal

/-- The `ℒ^{2r}`-**counting-measure** norm of a sequence `Z : ℤ → ℂ` is the `(1/(2r))`-power of
the `ℓ^{2r}`-sum of the `2r`-th powers of its moduli:

`eLpNorm Z (2r) count = (∑' n, ofReal ‖Z n‖^{2r}) ^ (1/(2r))`.

This is the bridge between Mathlib's `eLpNorm` and the elementary `ℓᵖ` quantity
`∑' n, ENNReal.ofReal (‖Z n‖ ^ p)` used in the statement of
`eLpNorm_count_le_of_tsum_le`. -/
private lemma eLpNorm_count_int_eq_tsum {r : ℕ} (hr : 1 ≤ r) (Z : ℤ → ℂ) :
    eLpNorm Z ((2 * r : ℕ) : ENNReal) (Measure.count : Measure ℤ)
      = (∑' n : ℤ, ENNReal.ofReal (‖Z n‖ ^ (2 * r))) ^ (1 / (2 * r : ℝ)) := by
  have hp0 : ((2 * r : ℕ) : ENNReal) ≠ 0 := by
    have : (2 * r) ≠ 0 := by omega
    exact_mod_cast this
  have hptop : ((2 * r : ℕ) : ENNReal) ≠ ∞ := ENNReal.natCast_ne_top _
  have hcast : ((2 * r : ℕ) : ℝ) = (2 * r : ℝ) := by push_cast; ring
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hp0 hptop]
  have hInt : ∫⁻ n : ℤ, ‖Z n‖ₑ ^ (((2 * r : ℕ) : ENNReal).toReal)
        ∂(Measure.count : Measure ℤ)
        = ∑' n : ℤ, ENNReal.ofReal (‖Z n‖ ^ (2 * r)) := by
    rw [ENNReal.toReal_natCast, MeasureTheory.lintegral_count]
    apply tsum_congr; intro n
    rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _), ENNReal.rpow_natCast]
  rw [hInt, ENNReal.toReal_natCast, hcast]

theorem eLpNorm_count_le_of_tsum_le {r : ℕ} (hr : 1 ≤ r) {X Y : ℤ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∑' n : ℤ, ENNReal.ofReal (‖X n‖ ^ (2 * r))
          ≤ ENNReal.ofReal C * ∑' n : ℤ, ENNReal.ofReal (‖Y n‖ ^ (2 * r))) :
    MeasureTheory.eLpNorm X ((2 * r : ℕ) : ENNReal)
        (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
      ≤ ENNReal.ofReal (C ^ (1 / (2 * r : ℝ))) *
        MeasureTheory.eLpNorm Y ((2 * r : ℕ) : ENNReal)
          (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
  -- the exponent `1/(2r)` is (strictly) positive since `r ≥ 1`
  have hexp_pos : (0 : ℝ) < 1 / (2 * r : ℝ) := by
    have h1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    positivity
  -- identify both `eLpNorm`s with the corresponding `ℓ^{2r}` sums
  rw [eLpNorm_count_int_eq_tsum hr X, eLpNorm_count_int_eq_tsum hr Y]
  -- take the `1/(2r)`-power of the hypothesis and split the product
  calc (∑' n : ℤ, ENNReal.ofReal (‖X n‖ ^ (2 * r))) ^ (1 / (2 * r : ℝ))
      ≤ (ENNReal.ofReal C * ∑' n : ℤ, ENNReal.ofReal (‖Y n‖ ^ (2 * r))) ^ (1 / (2 * r : ℝ)) :=
        ENNReal.rpow_le_rpow h (le_of_lt hexp_pos)
    _ = (ENNReal.ofReal C) ^ (1 / (2 * r : ℝ)) *
        (∑' n : ℤ, ENNReal.ofReal (‖Y n‖ ^ (2 * r))) ^ (1 / (2 * r : ℝ)) :=
        ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt hexp_pos)
    _ = ENNReal.ofReal (C ^ (1 / (2 * r : ℝ))) *
        (∑' n : ℤ, ENNReal.ofReal (‖Y n‖ ^ (2 * r))) ^ (1 / (2 * r : ℝ)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hC (le_of_lt hexp_pos)]

end Work.KMTAreas
