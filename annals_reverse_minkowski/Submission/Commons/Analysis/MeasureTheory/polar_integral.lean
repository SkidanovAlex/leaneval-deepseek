import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Commons.Analysis.MeasureTheory.polar_integral_prod

/-!
# Polar-coordinate integration, iterated (Fubini) form

Companion of `Commons.Analysis.MeasureTheory.polar_integral_prod`: for a
nontrivial finite-dimensional real inner-product space `V` and an integrable
`F : V → ℝ`, the integral of `F` over `V` equals the iterated integral, over the
unit sphere `θ` and over the positive ray `r`, of `F (r • θ)`, with respect to the
spherical surface measure `volume.toSphere` and the measure
`volumeIoiPow (finrank ℝ V - 1)` (density `r ↦ r^(dim-1)` on `(0, ∞)`).

We reduce to `polar_integral_prod` (which rewrites the integral over `V` as an
integral over `S × (0, ∞)`) and then apply Fubini's theorem
`MeasureTheory.integral_prod`.  Fubini requires the integrand
`(θ, r) ↦ F (r • θ)` to be integrable w.r.t. the product measure; this follows
from the integrability of `F` because `homeomorphUnitSphereProd V` is a
measure-preserving homeomorphism between `V ∖ {0}` and `S × (0, ∞)` carrying the
appropriate measures (`MeasurePreserving.integrable_comp_emb`).
-/

set_option linter.unusedSectionVars false

noncomputable section
open Set Function MeasureTheory Metric
open scoped Classical ENNReal NNReal Pointwise

namespace Commons.Analysis.MeasureTheory

theorem polar_integral
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] [FiniteDimensional ℝ V] [Nontrivial V]
    (F : V → ℝ) (hF : MeasureTheory.Integrable F MeasureTheory.volume) :
    (∫ x : V, F x) =
      ∫ θ : Metric.sphere (0 : V) 1,
        ∫ r : Set.Ioi (0 : ℝ), F (r.1 • (θ : V))
          ∂(MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ V - 1))
      ∂(MeasureTheory.volume.toSphere) := by
  let g : Metric.sphere (0 : V) 1 × Set.Ioi (0 : ℝ) → ℝ := fun p => F (p.2.1 • (p.1 : V))
  let h : ({0}ᶜ : Set V) ≃ₜ (Metric.sphere (0 : V) 1 × Set.Ioi (0 : ℝ)) :=
    homeomorphUnitSphereProd V
  have hmp : MeasurePreserving (h) (volume.comap (Subtype.val : ({0}ᶜ : Set V) → V))
      ((volume.toSphere).prod (Measure.volumeIoiPow (Module.finrank ℝ V - 1))) := by
    simpa [h] using (Measure.measurePreserving_homeomorphUnitSphereProd (μ := volume) (E := V))
  have hgh : ∀ x : ({0}ᶜ : Set V), g (h x) = F (x : V) := by
    intro x
    change F (((h x).2 : Set.Ioi (0 : ℝ)).1 • ((h x).1 : V)) = F (x : V)
    congr 1
    calc
      ((h x).2 : Set.Ioi (0 : ℝ)).1 • ((h x).1 : V)
          = ((h.symm (h x) : ({0}ᶜ : Set V)) : V) := by
            rw [homeomorphUnitSphereProd_symm_apply_coe (E := V) (x := h x)]
      _ = (x : V) := by
        congr 1
        exact h.left_inv x
  have hgi : Integrable g ((volume.toSphere).prod
      (Measure.volumeIoiPow (Module.finrank ℝ V - 1))) := by
    rw [← (hmp.integrable_comp_emb (h.measurableEmbedding) (g := g))]
    have hgval : Integrable (fun x : ({(0 : V)}ᶜ : Set V) => F (x : V))
        (volume.comap (Subtype.val : ({(0 : V)}ᶜ : Set V) → V)) := by
      have hFo : IntegrableOn F ({(0 : V)}ᶜ : Set V) volume := by
        dsimp [MeasureTheory.IntegrableOn]
        rw [restrict_compl_singleton (0 : V)]
        exact hF
      exact (integrableOn_iff_comap_subtypeVal (measurableSet_singleton (0 : V)).compl).mp hFo
    exact hgval.congr (ae_of_all _ (fun x => (hgh x).symm))
  calc
    (∫ x : V, F x) = ∫ p : Metric.sphere (0 : V) 1 × Set.Ioi (0 : ℝ), g p
          ∂((volume.toSphere).prod (Measure.volumeIoiPow (Module.finrank ℝ V - 1))) := by
      simpa [g] using (polar_integral_prod (V := V) F)
    _ = ∫ θ : Metric.sphere (0 : V) 1,
          ∫ r : Set.Ioi (0 : ℝ), g (θ, r) ∂(Measure.volumeIoiPow (Module.finrank ℝ V - 1))
        ∂(volume.toSphere) := by
      simpa using (MeasureTheory.integral_prod g hgi)
    _ = ∫ θ : Metric.sphere (0 : V) 1,
          ∫ r : Set.Ioi (0 : ℝ), F (r.1 • (θ : V))
            ∂(Measure.volumeIoiPow (Module.finrank ℝ V - 1))
        ∂(volume.toSphere) := by
      apply integral_congr_ae
      filter_upwards with θ
      apply integral_congr_ae
      filter_upwards with r
      simp [g]

end Commons.Analysis.MeasureTheory