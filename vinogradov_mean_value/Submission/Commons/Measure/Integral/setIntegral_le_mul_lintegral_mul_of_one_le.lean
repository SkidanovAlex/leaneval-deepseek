import Mathlib.MeasureTheory.Integral.Lebesgue.Add

namespace Commons.Measure.Integral

open MeasureTheory

theorem setIntegral_le_mul_lintegral_mul_of_one_le {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} {s : Set α} (hs : MeasurableSet s) {c : ENNReal} {Φ F : α → ENNReal} (hF : AEMeasurable F μ) (hΦm : AEMeasurable Φ μ) (hΦ : ∀ x ∈ s, (1 : ENNReal) ≤ c * Φ x) : MeasureTheory.lintegral (μ.restrict s) F ≤ c * MeasureTheory.lintegral μ (fun x => F x * Φ x) := by
  -- pointwise bound on `s`
  have hbound : ∀ x ∈ s, F x ≤ c * (F x * Φ x) := by
    intro x hx
    calc F x = F x * 1 := (mul_one _).symm
      _ ≤ F x * (c * Φ x) := mul_le_mul' le_rfl (hΦ x hx)
      _ = c * (F x * Φ x) := by rw [← mul_assoc, mul_comm (F x) c, mul_assoc]
  -- the bound holds almost everywhere for `μ.restrict s`
  have hae : ∀ᵐ x ∂(μ.restrict s), F x ≤ c * (F x * Φ x) :=
    (ae_restrict_mem hs).mono fun x hx => hbound x hx
  have h1 : ∫⁻ x, F x ∂(μ.restrict s) ≤ ∫⁻ x, c * (F x * Φ x) ∂(μ.restrict s) :=
    lintegral_mono_ae hae
  have h2 : ∫⁻ x, c * (F x * Φ x) ∂(μ.restrict s) = c * ∫⁻ x, (F x * Φ x) ∂(μ.restrict s) :=
    lintegral_const_mul'' c ((hF.mul hΦm).restrict)
  have h3 : ∫⁻ x, (F x * Φ x) ∂(μ.restrict s) ≤ ∫⁻ x, (F x * Φ x) ∂μ :=
    lintegral_mono' Measure.restrict_le_self le_rfl
  calc ∫⁻ x, F x ∂(μ.restrict s)
      ≤ ∫⁻ x, c * (F x * Φ x) ∂(μ.restrict s) := h1
    _ = c * ∫⁻ x, (F x * Φ x) ∂(μ.restrict s) := h2
    _ ≤ c * ∫⁻ x, (F x * Φ x) ∂μ := mul_le_mul' le_rfl h3

end Commons.Measure.Integral