import Mathlib

namespace Work.EKLComp

theorem sum_rpow_ediam_le {ι : Type*} [Fintype ι] {X : Type*} [PseudoEMetricSpace X]
    (u : ι → Set X) {δ d : ℝ} (hδ : 0 ≤ δ) (hd : 0 ≤ d)
    (h : ∀ i, Metric.ediam (u i) ≤ ENNReal.ofReal δ) :
    ∑ i, Metric.ediam (u i) ^ d ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * δ ^ d) := by
  have hcard : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := by positivity
  calc ∑ i, Metric.ediam (u i) ^ d
      ≤ ∑ _i : ι, (ENNReal.ofReal δ) ^ d :=
        Finset.sum_le_sum (fun i _ => ENNReal.rpow_le_rpow (h i) hd)
    _ = (Fintype.card ι : ENNReal) * (ENNReal.ofReal δ) ^ d := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ENNReal.ofReal (Fintype.card ι : ℝ) * (ENNReal.ofReal δ) ^ d := by
        rw [ENNReal.ofReal_natCast]
    _ = ENNReal.ofReal (Fintype.card ι : ℝ) * ENNReal.ofReal (δ ^ d) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hδ hd]
    _ = ENNReal.ofReal ((Fintype.card ι : ℝ) * δ ^ d) := by
        rw [ENNReal.ofReal_mul hcard]

end Work.EKLComp
