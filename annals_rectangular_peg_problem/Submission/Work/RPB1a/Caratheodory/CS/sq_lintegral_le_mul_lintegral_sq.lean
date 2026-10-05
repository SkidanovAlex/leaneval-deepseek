import Mathlib
import Submission.Work.RPB1a.Caratheodory.CS.rpow_half_mul_self
import Submission.Work.RPB1a.Caratheodory.CS.volume_Ioo_neg

namespace Work.RPB1a.Caratheodory.CS

open Complex Set Metric MeasureTheory
open scoped ENNReal Real Topology

/-- Cauchy–Schwarz for the lower integral on an arbitrary measure space, in the form
`(∫⁻ f) ^ 2 ≤ μ univ * ∫⁻ f ^ 2`.  This is Hölder's inequality with the conjugate
exponents `p = q = 2` applied to the pair `(f, 1)`. -/
lemma sq_lintegral_le_measure_mul_lintegral_sq {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    (∫⁻ a, f a ∂μ) ^ 2 ≤ (μ Set.univ) * ∫⁻ a, f a ^ 2 ∂μ := by
  have hpq : (2:ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have h1 : AEMeasurable (fun _ : α => (1:ℝ≥0∞)) μ := aemeasurable_const
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf h1
  simp only [Pi.mul_apply, mul_one, one_pow, lintegral_one, ENNReal.rpow_two] at hh
  calc (∫⁻ a, f a ∂μ) ^ 2 = (∫⁻ a, f a ∂μ) * (∫⁻ a, f a ∂μ) := by rw [pow_two]
    _ ≤ ((∫⁻ a, f a ^ 2 ∂μ) ^ (1/2:ℝ) * (μ Set.univ) ^ (1/2:ℝ)) *
        ((∫⁻ a, f a ^ 2 ∂μ) ^ (1/2:ℝ) * (μ Set.univ) ^ (1/2:ℝ)) := mul_le_mul' hh hh
    _ = (μ Set.univ) * ∫⁻ a, f a ^ 2 ∂μ := by
        rw [show ((∫⁻ a, f a ^ 2 ∂μ) ^ (1/2:ℝ) * (μ Set.univ) ^ (1/2:ℝ)) *
              ((∫⁻ a, f a ^ 2 ∂μ) ^ (1/2:ℝ) * (μ Set.univ) ^ (1/2:ℝ))
            = ((∫⁻ a, f a ^ 2 ∂μ) ^ (1/2:ℝ) * (∫⁻ a, f a ^ 2 ∂μ) ^ (1/2:ℝ)) *
              ((μ Set.univ) ^ (1/2:ℝ) * (μ Set.univ) ^ (1/2:ℝ)) by ac_rfl,
            rpow_half_mul_self, rpow_half_mul_self, mul_comm]

/-- Cauchy–Schwarz (Hölder with p = q = 2) for the lower integral over one period of angles. -/
theorem sq_lintegral_le_mul_lintegral_sq {g : ℝ → ℝ≥0∞} (hg : AEMeasurable g volume) :
    (∫⁻ θ in Ioo (-π) π, g θ) ^ 2 ≤ ENNReal.ofReal (2 * π) * ∫⁻ θ in Ioo (-π) π, g θ ^ 2 := by
  have hmain := sq_lintegral_le_measure_mul_lintegral_sq (volume.restrict (Ioo (-π) π)) hg.restrict
  have huniv : (volume.restrict (Ioo (-π) π)) Set.univ = ENNReal.ofReal (2 * π) := by
    rw [Measure.restrict_apply_univ, volume_Ioo_neg]
  simpa [huniv] using hmain

end Work.RPB1a.Caratheodory.CS
