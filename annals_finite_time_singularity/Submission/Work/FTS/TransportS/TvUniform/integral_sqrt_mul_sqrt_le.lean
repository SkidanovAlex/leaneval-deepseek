import Mathlib.MeasureTheory.Function.L2Space

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.TransportS.TvUniform

/-- Cauchy–Schwarz for the square roots of two nonnegative integrable functions. -/
theorem integral_sqrt_mul_sqrt_le {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    {p q : α → ℝ} (hpnn : 0 ≤ᵐ[μ] p) (hqnn : 0 ≤ᵐ[μ] q)
    (hp : MeasureTheory.Integrable p μ) (hq : MeasureTheory.Integrable q μ) :
    ∫ x, Real.sqrt (p x) * Real.sqrt (q x) ∂μ
      ≤ Real.sqrt (∫ x, p x ∂μ) * Real.sqrt (∫ x, q x ∂μ) := by
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hfnn : 0 ≤ᵐ[μ] fun x => Real.sqrt (p x) :=
    Filter.Eventually.of_forall fun x => Real.sqrt_nonneg _
  have hgnn : 0 ≤ᵐ[μ] fun x => Real.sqrt (q x) :=
    Filter.Eventually.of_forall fun x => Real.sqrt_nonneg _
  have hfaesm : AEStronglyMeasurable (fun x => Real.sqrt (p x)) μ :=
    hp.aemeasurable.sqrt.aestronglyMeasurable
  have hgaesm : AEStronglyMeasurable (fun x => Real.sqrt (q x)) μ :=
    hq.aemeasurable.sqrt.aestronglyMeasurable
  have hfsq : Integrable (fun x => (Real.sqrt (p x)) ^ 2) μ :=
    hp.congr (hpnn.mono fun x hx => (Real.sq_sqrt hx).symm)
  have hgsq : Integrable (fun x => (Real.sqrt (q x)) ^ 2) μ :=
    hq.congr (hqnn.mono fun x hx => (Real.sq_sqrt hx).symm)
  have hfmem : MemLp (fun x => Real.sqrt (p x)) (ENNReal.ofReal (2 : ℝ)) μ := by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    exact (memLp_two_iff_integrable_sq hfaesm).mpr hfsq
  have hgmem : MemLp (fun x => Real.sqrt (q x)) (ENNReal.ofReal (2 : ℝ)) μ := by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    exact (memLp_two_iff_integrable_sq hgaesm).mpr hgsq
  have hmain := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hpq hfnn hgnn hfmem hgmem
  have h1 : ∫ x, (Real.sqrt (p x)) ^ (2 : ℝ) ∂μ = ∫ x, p x ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hpnn] with x hx
    rw [Real.rpow_two, Real.sq_sqrt hx]
  have h2 : ∫ x, (Real.sqrt (q x)) ^ (2 : ℝ) ∂μ = ∫ x, q x ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hqnn] with x hx
    rw [Real.rpow_two, Real.sq_sqrt hx]
  calc ∫ x, Real.sqrt (p x) * Real.sqrt (q x) ∂μ
      ≤ (∫ x, (Real.sqrt (p x)) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))
          * (∫ x, (Real.sqrt (q x)) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := hmain
    _ = (∫ x, p x ∂μ) ^ (1 / (2 : ℝ)) * (∫ x, q x ∂μ) ^ (1 / (2 : ℝ)) := by rw [h1, h2]
    _ = Real.sqrt (∫ x, p x ∂μ) * Real.sqrt (∫ x, q x ∂μ) := by
        rw [Real.sqrt_eq_rpow (∫ x, p x ∂μ), Real.sqrt_eq_rpow (∫ x, q x ∂μ)]

end Work.FTS.TransportS.TvUniform
