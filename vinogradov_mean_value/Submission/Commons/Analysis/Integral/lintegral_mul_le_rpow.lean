import Mathlib.MeasureTheory.Integral.MeanInequalities

namespace Commons.Analysis.Integral

open MeasureTheory in
open scoped ENNReal in
theorem lintegral_mul_le_rpow {α : Type*} [MeasurableSpace α] (μ : Measure α) {p : ℝ} (hp : 2 < p)
    {u v : α → ℝ} (hu : ∀ x, 0 ≤ u x) (hv : ∀ x, 0 ≤ v x)
    (hmu : AEMeasurable u μ) (hmv : AEMeasurable v μ) :
    ∫⁻ x, ENNReal.ofReal (u x * v x) ∂μ ≤
      (∫⁻ x, ENNReal.ofReal (u x ^ (p / (p - 2))) ∂μ) ^ ((p - 2) / p) *
        (∫⁻ x, ENNReal.ofReal (v x ^ (p / 2)) ∂μ) ^ (2 / p) := by
  have hp0 : (0:ℝ) < p := by linarith
  have hp2 : (0:ℝ) < p - 2 := by linarith
  have hconj : (p / (p - 2)).HolderConjugate (p / 2) := by
    rw [Real.holderConjugate_iff]
    refine ⟨?_, ?_⟩
    · rw [one_lt_div hp2]; linarith
    · rw [inv_div, inv_div]
      field_simp
      ring
  have hf : AEMeasurable (fun x => ENNReal.ofReal (u x)) μ := hmu.ennreal_ofReal
  have hg : AEMeasurable (fun x => ENNReal.ofReal (v x)) μ := hmv.ennreal_ofReal
  have holder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hconj hf hg
  have hL : ∫⁻ x, ENNReal.ofReal (u x * v x) ∂μ
      = ∫⁻ x, ENNReal.ofReal (u x) * ENNReal.ofReal (v x) ∂μ := by
    apply lintegral_congr; intro x
    exact ENNReal.ofReal_mul (hu x)
  have hU : ∫⁻ x, ENNReal.ofReal (u x) ^ (p / (p - 2)) ∂μ
      = ∫⁻ x, ENNReal.ofReal (u x ^ (p / (p - 2))) ∂μ := by
    apply lintegral_congr; intro x
    exact ENNReal.ofReal_rpow_of_nonneg (hu x) (by positivity)
  have hV : ∫⁻ x, ENNReal.ofReal (v x) ^ (p / 2) ∂μ
      = ∫⁻ x, ENNReal.ofReal (v x ^ (p / 2)) ∂μ := by
    apply lintegral_congr; intro x
    exact ENNReal.ofReal_rpow_of_nonneg (hv x) (by positivity)
  simp only [Pi.mul_apply] at holder
  rw [hL.symm, hU, hV, one_div_div, one_div_div] at holder
  exact holder

end Commons.Analysis.Integral