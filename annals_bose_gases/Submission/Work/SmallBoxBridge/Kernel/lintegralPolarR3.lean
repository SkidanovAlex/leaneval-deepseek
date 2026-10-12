import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Polar coordinates (lintegral form) in `ℝ³`

The lower Lebesgue integral of any `ℝ≥0∞`-valued function on `ℝ³` can be computed by
integrating over the unit sphere times the radial half-line:

`∫⁻ p, g p = ∫⁻ b : sphere 0 1 × Ioi 0, g (b.2 • b.1) ∂(toSphere volume).prod (volumeIoiPow 2)`.

Because `dim ℝ³ = 3`, the power weight is `volumeIoiPow (3 - 1) = volumeIoiPow 2`.

The proof is a direct transport of the Mathlib identity
`Measure.measurePreserving_homeomorphUnitSphereProd`, which says that the polar
coordinates homeomorphism `{0}ᶜ ≃ₜ sphere 0 1 × Ioi 0` pushes `volume.comap Subtype.val`
to `volume.toSphere.prod (volumeIoiPow (finrank ℝ ℝ³ - 1))`.
The map is a measurable embedding, so the transport holds for arbitrary (not necessarily
measurable) `ℝ≥0∞`-valued integrands via `MeasurePreserving.lintegral_comp_emb`;
the missing point `0` is negligible and contributes nothing.
-/

open MeasureTheory

namespace Work.SmallBoxBridge.Kernel

theorem lintegralPolarR3 (g : EuclideanSpace ℝ (Fin 3) → ENNReal) :
    ∫⁻ (p : EuclideanSpace ℝ (Fin 3)), g p
      = ∫⁻ (b : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Set.Ioi (0 : ℝ)),
          g ((b.2 : ℝ) • (b.1 : EuclideanSpace ℝ (Fin 3)))
        ∂(MeasureTheory.Measure.toSphere (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))).prod
          (MeasureTheory.Measure.volumeIoiPow 2) := by
  -- Polar coordinates are a measure-preserving measurable embedding on the punctured space.
  have hmp :=
    Measure.measurePreserving_homeomorphUnitSphereProd
      (volume : Measure (EuclideanSpace ℝ (Fin 3)))
  have key := hmp.lintegral_comp_emb
    (Homeomorph.measurableEmbedding (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 3))))
    (fun b : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Set.Ioi (0 : ℝ) =>
      g ((b.2 : ℝ) • (b.1 : EuclideanSpace ℝ (Fin 3))))
  -- Removing the origin does not change the integral.
  have h1 : ∫⁻ (p : EuclideanSpace ℝ (Fin 3)), g p
      = ∫⁻ (p : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 3)))), g p
          ∂(volume.comap Subtype.val) := by
    rw [lintegral_subtype_comap (measurableSet_singleton (0 : EuclideanSpace ℝ (Fin 3))).compl]
    rw [restrict_compl_singleton]
  -- Transport along the polar coordinates homeomorphism.
  have h2 : ∫⁻ (a : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 3)))), g a.1
        ∂(volume.comap Subtype.val)
      = ∫⁻ (b : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Set.Ioi (0 : ℝ)),
          g ((b.2 : ℝ) • (b.1 : EuclideanSpace ℝ (Fin 3)))
          ∂((volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere.prod
            (Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1))) := by
    rw [← key]
    refine lintegral_congr fun a => ?_
    congr 1
    rw [homeomorphUnitSphereProd_apply_snd_coe, homeomorphUnitSphereProd_apply_fst_coe]
    rw [smul_inv_smul₀ (norm_ne_zero_iff.mpr a.2)]
  rw [h1, h2]
  norm_num

end Work.SmallBoxBridge.Kernel
