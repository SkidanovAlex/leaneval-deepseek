import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Measure.Integral

open MeasureTheory Filter

theorem tendsto_integral_norm_rpow_mul {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    {F : ℝ → α → ℂ} {f : α → ℂ} {w : α → ℝ} {M p : ℝ} (hM : 0 ≤ M) (hp : 0 < p)
    (hw : MeasureTheory.Integrable w μ) (hw0 : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hmeas : ∀ᶠ τ : ℝ in nhdsWithin 0 (Set.Ioi 0), AEMeasurable (F τ) μ)
    (hbdd : ∀ᶠ τ : ℝ in nhdsWithin 0 (Set.Ioi 0), ∀ᵐ x ∂μ, ‖F τ x‖ ≤ M)
    (hlim : ∀ᵐ x ∂μ, Filter.Tendsto (fun τ : ℝ => F τ x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f x))) :
    Filter.Tendsto (fun τ : ℝ => ∫ x, ‖F τ x‖ ^ p * w x ∂μ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ x, ‖f x‖ ^ p * w x ∂μ)) := by
  classical
  have hw_meas : AEMeasurable w μ := hw.aestronglyMeasurable.aemeasurable
  -- The dominating function.
  have hbound_int : Integrable (fun x => M ^ p * w x) μ := hw.const_mul (M ^ p)
  refine tendsto_integral_filter_of_dominated_convergence (fun x => M ^ p * w x) ?hF ?hbd
    hbound_int ?hlim
  · -- Almost everywhere strong measurability of the integrands.
    refine hmeas.mono fun τ hτ => ?_
    have hnorm : AEMeasurable (fun x => ‖F τ x‖) μ := hτ.norm
    have hrpow : AEMeasurable (fun x => ‖F τ x‖ ^ p) μ :=
      (Real.continuous_rpow_const hp.le).measurable.comp_aemeasurable hnorm
    exact (hrpow.mul hw_meas).aestronglyMeasurable
  · -- The dominating bound, eventually in τ.
    refine hbdd.mono fun τ hτ => ?_
    filter_upwards [hτ, hw0] with x hx_le hwx
    have hFx_nonneg : 0 ≤ ‖F τ x‖ := norm_nonneg _
    have hpow_le : ‖F τ x‖ ^ p ≤ M ^ p := Real.rpow_le_rpow hFx_nonneg hx_le hp.le
    have hprod_nonneg : 0 ≤ ‖F τ x‖ ^ p * w x :=
      mul_nonneg (Real.rpow_nonneg hFx_nonneg p) hwx
    rw [Real.norm_of_nonneg hprod_nonneg]
    exact mul_le_mul_of_nonneg_right hpow_le hwx
  · -- Pointwise convergence of the integrands.
    filter_upwards [hlim] with x hx
    have h1 : Tendsto (fun τ : ℝ => ‖F τ x‖) (nhdsWithin 0 (Set.Ioi 0)) (nhds ‖f x‖) :=
      hx.norm
    have h2 : Tendsto (fun τ : ℝ => ‖F τ x‖ ^ p) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (‖f x‖ ^ p)) :=
      (Real.continuousAt_rpow_const ‖f x‖ p (Or.inr hp.le)).tendsto.comp h1
    exact h2.mul_const (w x)

end Commons.Measure.Integral