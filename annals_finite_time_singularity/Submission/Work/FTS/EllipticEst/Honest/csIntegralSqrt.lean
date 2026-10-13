import Mathlib.MeasureTheory.Function.L2Space

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

theorem csIntegralSqrt {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    {F G : α → ℝ}
    (hF : AEMeasurable F μ) (hG : AEMeasurable G μ)
    (hF2 : MeasureTheory.Integrable (fun x => F x ^ 2) μ)
    (hG2 : MeasureTheory.Integrable (fun x => G x ^ 2) μ) :
    (∫ x, F x * G x ∂μ)
      ≤ Real.sqrt (∫ x, F x ^ 2 ∂μ) * Real.sqrt (∫ x, G x ^ 2 ∂μ) := by
  have hFmem : MeasureTheory.MemLp F 2 μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq hF.aestronglyMeasurable).2 hF2
  have hGmem : MeasureTheory.MemLp G 2 μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq hG.aestronglyMeasurable).2 hG2
  have hFmem' : MeasureTheory.MemLp F (ENNReal.ofReal 2) μ := by simpa using hFmem
  have hGmem' : MeasureTheory.MemLp G (ENNReal.ofReal 2) μ := by simpa using hGmem
  have hAB : MeasureTheory.Integrable (fun x => ‖F x‖ * ‖G x‖) μ :=
    hFmem.norm.integrable_mul hGmem.norm
  have hcs := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq (μ := μ) (f := F) (g := G)
    (p := 2) (q := 2) (by rw [Real.holderConjugate_iff]; norm_num) hFmem' hGmem'
  have hmono : (∫ x, F x * G x ∂μ) ≤ ∫ x, ‖F x‖ * ‖G x‖ ∂μ :=
    MeasureTheory.integral_mono (hFmem.integrable_mul hGmem) hAB (fun x => by
      show F x * G x ≤ ‖F x‖ * ‖G x‖
      rw [Real.norm_eq_abs, Real.norm_eq_abs, ← abs_mul]
      exact le_abs_self _)
  have h1 : (∫ a, ‖F a‖ ^ (2 : ℝ) ∂μ) = ∫ a, F a ^ 2 ∂μ := by
    congr 1 with a
    rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]
  have h2 : (∫ a, ‖G a‖ ^ (2 : ℝ) ∂μ) = ∫ a, G a ^ 2 ∂μ := by
    congr 1 with a
    rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]
  calc (∫ x, F x * G x ∂μ)
      ≤ ∫ x, ‖F x‖ * ‖G x‖ ∂μ := hmono
    _ ≤ (∫ a, ‖F a‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)
          * (∫ a, ‖G a‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := hcs
    _ = Real.sqrt (∫ a, F a ^ 2 ∂μ) * Real.sqrt (∫ a, G a ^ 2 ∂μ) := by
          rw [h1, h2, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

end Work.FTS.EllipticEst.Honest
