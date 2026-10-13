import Mathlib.MeasureTheory.Function.L2Space

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces

/-- Cauchy–Schwarz (Hölder with conjugate exponents `p = q = 2`) for two nonnegative
real-valued functions whose squares are integrable:
`∫ f * g ≤ sqrt (∫ f²) * sqrt (∫ g²)`. -/
theorem integral_mul_le_sqrt_mul_sqrt {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {f g : α → ℝ} (hf : ∀ y, 0 ≤ f y) (hg : ∀ y, 0 ≤ g y)
    (hfm : Measurable f) (hgm : Measurable g)
    (hfi : MeasureTheory.Integrable (fun y => f y ^ 2) μ)
    (hgi : MeasureTheory.Integrable (fun y => g y ^ 2) μ) :
    ∫ y, f y * g y ∂μ ≤ Real.sqrt (∫ y, f y ^ 2 ∂μ) * Real.sqrt (∫ y, g y ^ 2 ∂μ) := by
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  -- `L²`-membership of `f` and `g` from square-integrability.
  have hf2 : MeasureTheory.MemLp f (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    exact (MeasureTheory.memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).mpr hfi
  have hg2 : MeasureTheory.MemLp g (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    exact (MeasureTheory.memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).mpr hgi
  have hmain := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hpq
    (Filter.Eventually.of_forall hf) (Filter.Eventually.of_forall hg) hf2 hg2
  -- Rewrite the real powers `f ^ (2 : ℝ)` as squares and `x ^ (1/2)` as `sqrt x`.
  have h1 : ∫ y, f y ^ (2 : ℝ) ∂μ = ∫ y, f y ^ 2 ∂μ := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    simp only [Real.rpow_two]
  have h2 : ∫ y, g y ^ (2 : ℝ) ∂μ = ∫ y, g y ^ 2 ∂μ := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    simp only [Real.rpow_two]
  simpa [h1, h2, Real.sqrt_eq_rpow] using hmain

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces
