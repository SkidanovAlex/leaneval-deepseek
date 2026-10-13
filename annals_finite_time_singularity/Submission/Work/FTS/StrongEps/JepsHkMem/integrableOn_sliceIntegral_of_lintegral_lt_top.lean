import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.JepsHkMem

theorem integrableOn_sliceIntegral_of_lintegral_lt_top {F : ℝ → ℝ → ℝ}
    (hnn : ∀ z θ, 0 ≤ F z θ)
    (hsl : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ => F z θ) Work.Spaces.Iθ)
    (hmeas : MeasureTheory.AEStronglyMeasurable (fun q : ℝ × ℝ => F q.1 q.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hfin : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (F z θ)) < ⊤) :
    MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, F z θ) Work.Spaces.Iz := by
  have hGfin : MeasureTheory.HasFiniteIntegral (fun q : ℝ × ℝ => F q.1 q.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall (fun q : ℝ × ℝ => hnn q.1 q.2))]
    have hton := MeasureTheory.lintegral_lintegral
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun z θ => ENNReal.ofReal (F z θ))
      (hmeas.aemeasurable.ennreal_ofReal)
    rw [← hton]
    exact hfin
  have hGint : MeasureTheory.Integrable (fun q : ℝ × ℝ => F q.1 q.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := ⟨hmeas, hGfin⟩
  have hslice : MeasureTheory.Integrable
      (fun z => ∫ θ, ‖F z θ‖ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hGint.integral_norm_prod_left
  refine hslice.congr ?_
  filter_upwards with z
  exact MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun θ => Real.norm_of_nonneg (hnn z θ))

end Work.FTS.StrongEps.JepsHkMem
