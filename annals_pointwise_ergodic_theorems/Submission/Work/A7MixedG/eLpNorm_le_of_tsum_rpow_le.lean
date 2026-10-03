import Mathlib
import Submission.Work.KMTAreas.A7.fiberVarSamplingLargeLoss_bdd
import Submission.Port.Aesm

namespace Work.A7MixedG

open MeasureTheory

/-- Comparison of `ℓᵖ` norms (with respect to counting measure on `ℤ`) from an
inequality of the `p`-th power sums: if `∑ Fᵖ ≤ C · ∑ Wᵖ` then
`‖F‖_{ℓᵖ} ≤ C^{1/p} · ‖W‖_{ℓᵖ}`. -/
theorem eLpNorm_le_of_tsum_rpow_le {F W : ℤ → ENNReal} {p : ℝ} (hp : 0 < p) {C : ℝ} (hC : 0 < C)
    (h : (∑' x : ℤ, (F x) ^ p) ≤ ENNReal.ofReal C * (∑' x : ℤ, (W x) ^ p)) :
    MeasureTheory.eLpNorm F (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C ^ (1 / p)) *
        MeasureTheory.eLpNorm W (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  have hpne : (ENNReal.ofReal p) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hp
  have hptop : (ENNReal.ofReal p) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hpne hptop,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hpne hptop]
  simp only [ENNReal.toReal_ofReal hp.le]
  simp_rw [enorm_eq_self]
  rw [lintegral_count, lintegral_count]
  calc (∑' x : ℤ, F x ^ p) ^ (1 / p)
      ≤ (ENNReal.ofReal C * (∑' x : ℤ, W x ^ p)) ^ (1 / p) :=
        ENNReal.rpow_le_rpow h (by positivity)
    _ = (ENNReal.ofReal C) ^ (1 / p) * (∑' x : ℤ, W x ^ p) ^ (1 / p) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
    _ = ENNReal.ofReal (C ^ (1 / p)) * (∑' x : ℤ, W x ^ p) ^ (1 / p) := by
        rw [ENNReal.ofReal_rpow_of_pos hC]

end Work.A7MixedG
