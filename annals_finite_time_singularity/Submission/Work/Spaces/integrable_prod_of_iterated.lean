import Mathlib.MeasureTheory.Integral.Prod

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces

theorem integrable_prod_of_iterated {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β}
    [MeasureTheory.SFinite μ] [MeasureTheory.SFinite ν]
    {G : α → β → ℝ}
    (hnn : ∀ a b, 0 ≤ G a b)
    (hAE : MeasureTheory.AEStronglyMeasurable (Function.uncurry G) (μ.prod ν))
    (hslice : ∀ᵐ a ∂μ, MeasureTheory.Integrable (fun b => G a b) ν)
    (houter : MeasureTheory.Integrable (fun a => ∫ b, G a b ∂ν) μ) :
    MeasureTheory.Integrable (Function.uncurry G) (μ.prod ν) ∧
      ∫ p, G p.1 p.2 ∂(μ.prod ν) = ∫ a, (∫ b, G a b ∂ν) ∂μ := by
  -- Pointwise nonnegativity turns the norm in `integrable_prod_iff` into `G` itself.
  have hkey : (fun x : α => ∫ y, ‖Function.uncurry G (x, y)‖ ∂ν) =
      (fun x => ∫ y, G x y ∂ν) := by
    funext x
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun y => by
        simp only [Function.uncurry_apply_pair, Real.norm_of_nonneg (hnn x y)])
  have hIntegrable : MeasureTheory.Integrable (Function.uncurry G) (μ.prod ν) := by
    rw [MeasureTheory.integrable_prod_iff hAE]
    exact ⟨hslice, by rw [hkey]; exact houter⟩
  exact ⟨hIntegrable, (MeasureTheory.integral_integral hIntegrable).symm⟩

end Work.Spaces
