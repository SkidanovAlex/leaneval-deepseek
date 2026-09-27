import Mathlib

namespace Work.EKLComp

open MeasureTheory Set

-- Window average along a measure preserving flow: measurability, integrability and mean.
-- Proof: `MeasureTheory.StronglyMeasurable.integral_prod_left'` applied with the measure
-- `volume.restrict (Ioc 0 δ)` gives measurability of `x ↦ ∫ τ, f (φ τ x) ∂(volume.restrict (Ioc 0 δ))`,
-- which `intervalIntegral.integral_of_le` identifies with the interval integral.
-- Integrability of `(fun p : ℝ × X => f (φ p.1 p.2))` on the product measure follows from
-- Tonelli and `MeasurePreserving` of each `φ τ`; then `intervalIntegral_integral_swap` gives
-- `∫ x, ∫ τ, f (φ τ x) = ∫ τ, ∫ x, f (φ τ x) = δ * ∫ x, f x`.
theorem measurable_integrable_avg_over {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.SFinite μ] (φ : ℝ → X → X)
    (hmp : ∀ τ : ℝ, MeasureTheory.MeasurePreserving (φ τ) μ μ)
    (f : X → ℝ) (hfm : Measurable (fun p : ℝ × X => f (φ p.1 p.2)))
    (hfi : MeasureTheory.Integrable f μ) (δ : ℝ) (hδ : 0 < δ) :
    Measurable (fun x => δ⁻¹ * ∫ τ in (0:ℝ)..δ, f (φ τ x)) ∧
    MeasureTheory.Integrable (fun x => δ⁻¹ * ∫ τ in (0:ℝ)..δ, f (φ τ x)) μ ∧
    ∫ x, (δ⁻¹ * ∫ τ in (0:ℝ)..δ, f (φ τ x)) ∂μ = ∫ x, f x ∂μ := by
  have hδ' : (0:ℝ) ≤ δ := le_of_lt hδ
  let ν : Measure ℝ := volume.restrict (Set.Ioc 0 δ)
  let F : ℝ × X → ℝ := fun p => f (φ p.1 p.2)
  have hFm : Measurable F := hfm
  -- Pointwise identification of the interval integral with the integral against `ν`.
  have htransfer : ∀ x : X, (∫ τ in (0:ℝ)..δ, f (φ τ x)) = ∫ τ, F (τ, x) ∂ν := by
    intro x
    rw [intervalIntegral.integral_of_le hδ']
  -- Integrability of the joint function on the product measure.
  have hInt : Integrable F (ν.prod μ) := by
    refine ⟨hFm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    rw [lintegral_prod (fun p : ℝ × X => ‖F p‖ₑ) hFm.aestronglyMeasurable.enorm]
    have hpt : ∀ τ : ℝ, ∫⁻ x, ‖F (τ, x)‖ₑ ∂μ = ∫⁻ x, ‖f x‖ₑ ∂μ := by
      intro τ
      have hmap : Measure.map (φ τ) μ = μ := (hmp τ).map_eq
      have hA : AEMeasurable (fun x => ‖f x‖ₑ) (Measure.map (φ τ) μ) := by
        rw [hmap]; exact hfi.aestronglyMeasurable.enorm
      have hab : ∫⁻ y, ‖f y‖ₑ ∂(Measure.map (φ τ) μ) = ∫⁻ x, ‖f (φ τ x)‖ₑ ∂μ :=
        lintegral_map' hA (hmp τ).measurable.aemeasurable
      rw [hmap] at hab
      rw [hab]
    simp_rw [hpt]
    rw [lintegral_const]
    apply ENNReal.mul_lt_top
    · exact hasFiniteIntegral_iff_enorm.mp hfi.2
    · have hvol : ν Set.univ = ENNReal.ofReal δ := by
        show (volume.restrict (Set.Ioc 0 δ)) Set.univ = ENNReal.ofReal δ
        rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc,
          sub_zero]
      rw [hvol]; exact ENNReal.ofReal_lt_top
  -- Measurability of the averaged function.
  have hmeas : Measurable (fun x => ∫ τ in (0:ℝ)..δ, f (φ τ x)) := by
    have hsm : StronglyMeasurable (fun x => ∫ τ, F (τ, x) ∂ν) :=
      StronglyMeasurable.integral_prod_left' (μ := ν) hFm.stronglyMeasurable
    have heq : (fun x => ∫ τ, F (τ, x) ∂ν) = fun x => ∫ τ in (0:ℝ)..δ, f (φ τ x) := by
      funext x; exact (htransfer x).symm
    rw [← heq]
    exact hsm.measurable
  -- Integrability of the averaged function.
  have hint : Integrable (fun x => ∫ τ in (0:ℝ)..δ, f (φ τ x)) μ := by
    have h : Integrable (fun x => ∫ τ, F (τ, x) ∂ν) μ :=
      Integrable.integral_prod_right (μ := ν) (ν := μ) hInt
    have heq : (fun x => ∫ τ, F (τ, x) ∂ν) = fun x => ∫ τ in (0:ℝ)..δ, f (φ τ x) := by
      funext x; exact (htransfer x).symm
    exact heq ▸ h
  -- Mean value.
  have hpt2 : ∀ τ : ℝ, ∫ x, f (φ τ x) ∂μ = ∫ x, f x ∂μ := by
    intro τ
    have hmap : Measure.map (φ τ) μ = μ := (hmp τ).map_eq
    have hAE : AEStronglyMeasurable f (Measure.map (φ τ) μ) := by rw [hmap]; exact hfi.1
    have h := integral_map (μ := μ) (φ := φ τ) (hmp τ).measurable.aemeasurable hAE
    rw [hmap] at h
    rw [← h]
  have hIntU : Integrable F ((volume.restrict (Set.uIoc 0 δ)).prod μ) := by
    rw [Set.uIoc_of_le hδ']; exact hInt
  have hswap := intervalIntegral_integral_swap (μ := μ) (a := 0) (b := δ)
    (f := fun τ x => f (φ τ x)) hIntU
  have hL : ∫ τ in (0:ℝ)..δ, (∫ x, f (φ τ x) ∂μ) = δ * ∫ x, f x ∂μ := by
    simp_rw [hpt2]
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  have hmean : ∫ x, (∫ τ in (0:ℝ)..δ, f (φ τ x)) ∂μ = δ * ∫ x, f x ∂μ := by
    rw [← hswap]; exact hL
  refine ⟨hmeas.const_mul δ⁻¹, hint.const_mul δ⁻¹, ?_⟩
  rw [MeasureTheory.integral_const_mul, hmean, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hδ),
    one_mul]

end Work.EKLComp
