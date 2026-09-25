import Mathlib
import Submission.Work.BourgainPlan.Oscillation.commons_deps

/-!
# Plancherel's identity for the Fourier coefficients on `(0,1]`

The Plancherel identity for the Fourier coefficients of an `L²`-function on `(0,1]`,
in the exact `∫⁻`/counting-measure form needed by the oscillation block estimates:

`∑_{n ∈ ℤ} |ĉ_n|² = ∫_0^1 |F|²`.

It is obtained from Mathlib's Parseval identity `tsum_sq_fourierCoeffOn`
(`∑' i, ‖fourierCoeffOn hab f i‖ ^ 2 = (b - a)⁻¹ • ∫ x in a..b, ‖f x‖ ^ 2`)
by rewriting both sides in terms of `ENNReal.ofReal` (`lintegral_count` on the left,
`ENNReal.ofReal_tsum_of_nonneg` and `ofReal_integral_eq_lintegral_ofReal` on the right).
-/

open MeasureTheory
open scoped ENNReal

namespace Work.BourgainPlan.Oscillation

theorem oscBlock_plancherel (F : ℝ → ℂ)
    (hF : MeasureTheory.MemLp F 2 (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1))) :
    ∫⁻ n : ℤ, ‖fourierCoeffOn (by norm_num : (0:ℝ) < 1) F n‖ₑ ^ (2 : ℝ)
        ∂MeasureTheory.Measure.count
      = ∫⁻ θ, ‖F θ‖ₑ ^ (2 : ℝ) ∂(MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1)) := by
  have hcoe : ∀ n : ℤ, ‖fourierCoeffOn (by norm_num : (0:ℝ) < 1) F n‖ₑ ^ (2 : ℝ)
      = ENNReal.ofReal (‖fourierCoeffOn (by norm_num : (0:ℝ) < 1) F n‖ ^ 2) := by
    intro n
    rw [ENNReal.rpow_two, ← ofReal_norm]
    exact (ENNReal.ofReal_pow (norm_nonneg _) 2).symm
  have hsum : Summable (fun n : ℤ => ‖fourierCoeffOn (by norm_num : (0:ℝ) < 1) F n‖ ^ 2) := by
    have h := hasSum_sq_fourierCoeffOn (a := (0:ℝ)) (b := 1) (by norm_num) hF
    rw [tsub_zero, inv_one, one_smul] at h
    exact h.summable
  have htsum : ∑' (n : ℤ), ‖fourierCoeffOn (by norm_num : (0:ℝ) < 1) F n‖ ^ 2
      = ∫ x in (0:ℝ)..1, ‖F x‖ ^ 2 := by
    have h := hasSum_sq_fourierCoeffOn (a := (0:ℝ)) (b := 1) (by norm_num) hF
    rw [tsub_zero, inv_one, one_smul] at h
    exact h.tsum_eq
  have hcoe2 : ∀ θ : ℝ, ‖F θ‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖F θ‖ ^ 2) := by
    intro θ
    rw [ENNReal.rpow_two, ← ofReal_norm]
    exact (ENNReal.ofReal_pow (norm_nonneg _) 2).symm
  have hInt : Integrable (fun θ : ℝ => ‖F θ‖ ^ 2) (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    have := hF.integrable_norm_rpow (by norm_num : (2:ℝ≥0∞) ≠ 0) (by norm_num : (2:ℝ≥0∞) ≠ ∞)
    simpa using this
  calc ∫⁻ n : ℤ, ‖fourierCoeffOn (by norm_num : (0:ℝ) < 1) F n‖ₑ ^ (2 : ℝ)
        ∂MeasureTheory.Measure.count
      = ∑' n : ℤ, ENNReal.ofReal (‖fourierCoeffOn (by norm_num : (0:ℝ) < 1) F n‖ ^ 2) := by
        rw [MeasureTheory.lintegral_count]
        simp_rw [hcoe]
    _ = ENNReal.ofReal (∑' n : ℤ, ‖fourierCoeffOn (by norm_num : (0:ℝ) < 1) F n‖ ^ 2) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum).symm
    _ = ENNReal.ofReal (∫ x in (0:ℝ)..1, ‖F x‖ ^ 2) := by rw [htsum]
    _ = ENNReal.ofReal (∫ θ, ‖F θ‖ ^ 2 ∂(volume.restrict (Set.Ioc (0:ℝ) 1))) := by
        rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    _ = ∫⁻ θ, ‖F θ‖ₑ ^ (2 : ℝ) ∂(MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1)) := by
        simp_rw [hcoe2]
        rw [← ofReal_integral_eq_lintegral_ofReal hInt
          (Filter.Eventually.of_forall fun θ => by positivity)]

end Work.BourgainPlan.Oscillation
