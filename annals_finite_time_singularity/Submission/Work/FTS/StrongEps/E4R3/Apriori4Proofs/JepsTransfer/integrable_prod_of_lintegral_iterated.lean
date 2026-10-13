import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer

open MeasureTheory

/-- If the iterated (Tonelli) lintegral of `‖F z θ‖` over `z ∈ (0,∞)`, `θ ∈ (0,π/2)` is
finite and `F` is a.e. strongly measurable on the product region, then `F` is integrable
there.  The region integral `volume.restrict (Ioi 0 ×ˢ Ioo 0 (π/2))` is the product of the
two slice measures (`Measure.prod_restrict`), and the iterated integral equals the integral
over that product (`lintegral_lintegral`). -/
theorem integrable_prod_of_lintegral_iterated {F : ℝ → ℝ → ℝ}
    (hm : MeasureTheory.AEStronglyMeasurable (Function.uncurry F)
      (MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))))
    (hfin : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (Real.pi / 2),
        ENNReal.ofReal ‖F z θ‖) ≠ ⊤) :
    MeasureTheory.Integrable (Function.uncurry F)
      (MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) := by
  set s : Set ℝ := Set.Ioi 0
  set t : Set ℝ := Set.Ioo 0 (Real.pi / 2)
  -- the restricton of the product measure to the product set is the product of restrictions
  have hμeq : (volume : Measure (ℝ × ℝ)).restrict (s ×ˢ t)
      = (volume.restrict s).prod (volume.restrict t) := by
    show (volume.prod volume).restrict (s ×ˢ t)
      = (volume.restrict s).prod (volume.restrict t)
    rw [← Measure.prod_restrict s t]
  -- a.e. strong measurability of the `ENNReal`-valued integrand for Tonelli
  have hmeas : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal ‖F p.1 p.2‖)
      ((volume.restrict s).prod (volume.restrict t)) := by
    have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => F p.1 p.2)
        ((volume.restrict s).prod (volume.restrict t)) := by
      rw [← hμeq]
      exact hm
    exact h1.norm.aemeasurable.ennreal_ofReal
  -- Tonelli: the product integral is the iterated integral
  have hprod : (∫⁻ p, ENNReal.ofReal ‖F p.1 p.2‖
        ∂((volume.restrict s).prod (volume.restrict t)))
      = (∫⁻ z, ∫⁻ θ, ENNReal.ofReal ‖F z θ‖
        ∂(volume.restrict t) ∂(volume.restrict s)) := by
    have := lintegral_lintegral (μ := volume.restrict s) (ν := volume.restrict t)
      (f := fun z θ => ENNReal.ofReal ‖F z θ‖) hmeas
    simpa only [Function.uncurry] using this.symm
  -- hence the product integral is finite
  have hne : (∫⁻ p, ENNReal.ofReal ‖F p.1 p.2‖
        ∂((volume.restrict s).prod (volume.restrict t))) ≠ ⊤ := by
    rw [hprod]
    exact hfin
  refine ⟨hm, ?_⟩
  rw [hasFiniteIntegral_iff_norm, lt_top_iff_ne_top, hμeq]
  simpa only [Function.uncurry] using hne

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer
