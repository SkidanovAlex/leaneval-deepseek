import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Topology.Separation.CompletelyRegular

/-!
# Polar-coordinate integration on a finite-dimensional real inner-product space

For `V` a nontrivial finite-dimensional real inner-product space, the map
`x ↦ (‖x‖⁻¹ • x, ‖x‖)` is a measure-preserving homeomorphism between
`V ∖ {0}` (with Lebesgue `volume`) and the product
`Metric.sphere (0 : V) 1 × Set.Ioi (0 : ℝ)` carrying the product of the
spherical surface measure `volume.toSphere` and the measure
`volumeIoiPow (finrank ℝ V - 1)` (the density `r ↦ r^(dim-1)` on the
positive ray — see Mathlib's `Mathlib.MeasureTheory.Constructions.HaarToSphere`).
Removing the origin is harmless since singletons are null for `volume`
(`[Nontrivial V]`).  This yields the classical polar-coordinate identity
`∫ x, F x = ∫_{S × (0,∞)} F (r • θ) dσ d(r^(dim-1))` with no integrability
hypothesis (both sides are Bochner integrals, zero unless integrable).
-/

set_option linter.unusedSectionVars false

noncomputable section
open Set Function MeasureTheory Metric
open scoped Classical ENNReal NNReal Pointwise

namespace Commons.Analysis.MeasureTheory

/-- The unit sphere in the real inner-product space `V`. -/
abbrev UnitSphere (V : Type*) [NormedAddCommGroup V] := Metric.sphere (0 : V) 1

theorem polar_integral_prod
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] [FiniteDimensional ℝ V] [Nontrivial V]
    (F : V → ℝ) :
    (∫ x : V, F x) =
      ∫ p : Metric.sphere (0 : V) 1 × Set.Ioi (0 : ℝ),
        F (p.2.1 • (p.1 : V))
        ∂((MeasureTheory.volume.toSphere).prod
          (MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ V - 1))) := by
  let g : UnitSphere V × Set.Ioi (0 : ℝ) → ℝ := fun p => F (p.2.1 • (p.1 : V))
  let h : ({0}ᶜ : Set V) ≃ₜ (UnitSphere V × Set.Ioi (0 : ℝ)) := homeomorphUnitSphereProd V
  have hmp : MeasurePreserving (h) (volume.comap (Subtype.val : ({0}ᶜ : Set V) → V))
      ((volume.toSphere).prod (Measure.volumeIoiPow (Module.finrank ℝ V - 1))) := by
    simpa [h] using (Measure.measurePreserving_homeomorphUnitSphereProd (μ := volume) (E := V))
  have hmain : (∫ x : ({0}ᶜ : Set V), g (h x) ∂(volume.comap (Subtype.val : ({0}ᶜ : Set V) → V)))
      = ∫ p : UnitSphere V × Set.Ioi (0 : ℝ), g p
          ∂((volume.toSphere).prod (Measure.volumeIoiPow (Module.finrank ℝ V - 1))) := by
    simpa using (MeasurePreserving.integral_comp hmp (h.measurableEmbedding) g)
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
  calc
    (∫ x : V, F x) = ∫ x : V, F x ∂(volume.restrict ({0} : Set V)ᶜ) := by
      rw [restrict_compl_singleton (0 : V)]
    _ = ∫ x : ({(0 : V)}ᶜ : Set V), F (x : V) ∂(volume.comap (Subtype.val : ({(0 : V)}ᶜ : Set V) → V)) := by
      rw [← integral_subtype_comap (measurableSet_singleton (0 : V)).compl (fun x : V => F x)]
    _ = (∫ x : ({0}ᶜ : Set V), g (h x) ∂(volume.comap (Subtype.val : ({0}ᶜ : Set V) → V))) := by
      refine integral_congr_ae ?_
      filter_upwards with x
      exact (hgh x).symm
    _ = ∫ p : UnitSphere V × Set.Ioi (0 : ℝ), g p
          ∂((volume.toSphere).prod (Measure.volumeIoiPow (Module.finrank ℝ V - 1))) := hmain
    _ = ∫ p : Metric.sphere (0 : V) 1 × Set.Ioi (0 : ℝ), F (p.2.1 • (p.1 : V))
          ∂((MeasureTheory.volume.toSphere).prod
            (MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ V - 1))) := by
      simp [g]

end Commons.Analysis.MeasureTheory