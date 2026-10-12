import Mathlib.MeasureTheory.Function.L1Space.Integrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Measure.Integral

open MeasureTheory
open scoped ENNReal

/-- Corrected (s-finite) version of `integrable_uncurry_of_lintegral_le`.  The unrestricted
version is FALSE (the iterated integral over `ν` can be finite while the integral over `μ.prod ν`
is infinite; take `μ` the category/"meagre" measure on `ℝ`, `ν` Lebesgue measure).  With
`[SFinite μ]` and `[SFinite ν]` both iterated integrals equal the product integral by Tonelli. -/
theorem integrable_uncurry_of_lintegral_le_sfinite {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {f : α → β → ℝ} {g : β → ENNReal}
    (hmeas : AEStronglyMeasurable (Function.uncurry f) (μ.prod ν))
    (hg : (∫⁻ p, g p ∂ν) ≠ ⊤)
    (hbm : ∀ᵐ p ∂ν, (∫⁻ t, ENNReal.ofReal ‖f t p‖ ∂μ) ≤ g p) :
    Integrable (Function.uncurry f) (μ.prod ν) := by
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hprod : ∫⁻ q, ‖Function.uncurry f q‖ₑ ∂(μ.prod ν)
      = ∫⁻ p, (∫⁻ t, ENNReal.ofReal ‖f t p‖ ∂μ) ∂ν := by
    rw [lintegral_prod_symm (fun q : α × β => ‖Function.uncurry f q‖ₑ)
      hmeas.aemeasurable.enorm]
    apply lintegral_congr; intro p
    apply lintegral_congr; intro t
    simp only [Function.uncurry]
    rw [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs]
  rw [hprod]
  exact lt_of_le_of_lt (lintegral_mono_ae hbm) (lt_top_iff_ne_top.mpr hg)

end Commons.Measure.Integral