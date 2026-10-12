import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1S.PiCoordMeanL2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.PiAnova.fibreCS_prod`

The *fibre* Cauchy–Schwarz bound for the two-factor product measure
`ν.prod (Measure.pi (fun _ : Fin N => ν))`: if `Ψ` is a.e. strongly measurable and `Ψ²` is
integrable on the product, then

`∫ r, (∫ z, Ψ (z, r) ∂ν)² ∂π ≤ (ν univ).toReal · ∫ p, Ψ p ² ∂(ν.prod π)`,
with `π = Measure.pi (fun _ : Fin N => ν)`.

Proof.  For a.e. `r` the slice `z ↦ Ψ (z, r)` is a.e. strongly measurable and its square is
`ν`-integrable (`AEStronglyMeasurable.prodMk_right`, `Integrable.prod_left_ae`), so the fibre
Cauchy–Schwarz `Work.BoseFixB1S.sq_integral_le_measure_mul_integral_sq` applies pointwise.
Integrating the resulting a.e. inequality against `π` (`integral_mono_ae`, with
`Integrable.integral_prod_right` giving the dominating function) and evaluating the iterated
integral by Tonelli (`MeasureTheory.integral_prod_symm`) gives the claim.
-/

namespace Work.BoseFixB1S.PiAnova

open MeasureTheory

theorem fibreCS_prod {α : Type*} [MeasurableSpace α] [Nonempty α]
    (ν : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure ν] {N : ℕ}
    {Ψ : α × (Fin N → α) → ℝ}
    (hΨ : MeasureTheory.AEStronglyMeasurable Ψ
      (ν.prod (MeasureTheory.Measure.pi (fun _ : Fin N => ν))))
    (hΨ2 : MeasureTheory.Integrable (fun p => (Ψ p) ^ 2)
      (ν.prod (MeasureTheory.Measure.pi (fun _ : Fin N => ν)))) :
    ∫ r, (∫ z, Ψ (z, r) ∂ν) ^ 2 ∂(MeasureTheory.Measure.pi (fun _ : Fin N => ν))
      ≤ (ν Set.univ).toReal
        * ∫ p, (Ψ p) ^ 2 ∂(ν.prod (MeasureTheory.Measure.pi (fun _ : Fin N => ν))) := by
  -- a.e. strong measurability of the slices
  have hsliceSM : ∀ᵐ r ∂(Measure.pi (fun _ : Fin N => ν)),
      AEStronglyMeasurable (fun z => Ψ (z, r)) ν := hΨ.prodMk_right
  -- a.e. square-integrability of the slices
  have hsliceL2 : ∀ᵐ r ∂(Measure.pi (fun _ : Fin N => ν)),
      Integrable (fun z => (Ψ (z, r)) ^ 2) ν := hΨ2.prod_left_ae
  -- the pointwise fibre Cauchy–Schwarz
  have hpoint : ∀ᵐ r ∂(Measure.pi (fun _ : Fin N => ν)),
      (∫ z, Ψ (z, r) ∂ν) ^ 2 ≤ (ν Set.univ).toReal * ∫ z, (Ψ (z, r)) ^ 2 ∂ν := by
    filter_upwards [hsliceSM, hsliceL2] with r hsm hl2
    exact Work.BoseFixB1S.sq_integral_le_measure_mul_integral_sq hsm hl2
  -- the dominating function is integrable
  have hG : Integrable (fun r => ∫ z, (Ψ (z, r)) ^ 2 ∂ν)
      (Measure.pi (fun _ : Fin N => ν)) := hΨ2.integral_prod_right
  have hdom : Integrable (fun r => (ν Set.univ).toReal * ∫ z, (Ψ (z, r)) ^ 2 ∂ν)
      (Measure.pi (fun _ : Fin N => ν)) := hG.const_mul _
  -- so the left-hand integrand is integrable
  have hInt : Integrable (fun r => (∫ z, Ψ (z, r) ∂ν) ^ 2)
      (Measure.pi (fun _ : Fin N => ν)) := by
    refine Integrable.mono' hdom ((hΨ.prod_swap).integral_prod_right' |>.pow 2) ?_
    filter_upwards [hpoint] with r hr
    rwa [Real.norm_of_nonneg (sq_nonneg _)]
  -- Tonelli for the iterated integral
  have hFub : ∫ r, (∫ z, (Ψ (z, r)) ^ 2 ∂ν) ∂(Measure.pi (fun _ : Fin N => ν))
      = ∫ p, (Ψ p) ^ 2 ∂(ν.prod (Measure.pi (fun _ : Fin N => ν))) :=
    (integral_prod_symm (fun p : α × (Fin N → α) => (Ψ p) ^ 2) hΨ2).symm
  calc ∫ r, (∫ z, Ψ (z, r) ∂ν) ^ 2 ∂(Measure.pi (fun _ : Fin N => ν))
      ≤ ∫ r, (ν Set.univ).toReal * (∫ z, (Ψ (z, r)) ^ 2 ∂ν)
          ∂(Measure.pi (fun _ : Fin N => ν)) := integral_mono_ae hInt hdom hpoint
    _ = (ν Set.univ).toReal
          * ∫ r, (∫ z, (Ψ (z, r)) ^ 2 ∂ν) ∂(Measure.pi (fun _ : Fin N => ν)) :=
        integral_const_mul _ _
    _ = (ν Set.univ).toReal
          * ∫ p, (Ψ p) ^ 2 ∂(ν.prod (Measure.pi (fun _ : Fin N => ν))) := by rw [hFub]

end Work.BoseFixB1S.PiAnova
