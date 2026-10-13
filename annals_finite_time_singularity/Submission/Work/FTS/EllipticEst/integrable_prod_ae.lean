import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.integrable_prod_of_iterated

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

theorem integrable_prod_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β}
    [MeasureTheory.SFinite μ] [MeasureTheory.SFinite ν] {G : α → β → ℝ}
    (hnn : ∀ᵐ a ∂μ, ∀ᵐ b ∂ν, 0 ≤ G a b)
    (hAE : MeasureTheory.AEStronglyMeasurable (Function.uncurry G) (μ.prod ν))
    (hslice : ∀ᵐ a ∂μ, MeasureTheory.Integrable (fun b => G a b) ν)
    (houter : MeasureTheory.Integrable (fun a => ∫ b, G a b ∂ν) μ) :
    MeasureTheory.Integrable (Function.uncurry G) (μ.prod ν) := by
  -- The converse direction of Fubini for products (`integrable_prod_iff`) asks for
  -- integrability of the *norm* iterated integral `a ↦ ∫ b, ‖G a b‖ ∂ν`. Almost
  -- everywhere nonnegativity makes it agree a.e. with the given signed iterated
  -- integral `a ↦ ∫ b, G a b ∂ν`, so it is integrable by `Integrable.congr`.
  refine (MeasureTheory.integrable_prod_iff hAE).2 ⟨hslice, ?_⟩
  refine houter.congr ?_
  filter_upwards [hnn] with a ha
  refine MeasureTheory.integral_congr_ae (ha.mono fun b hb => ?_)
  simp only [Function.uncurry_apply_pair, Real.norm_of_nonneg hb]

end Work.FTS.EllipticEst
