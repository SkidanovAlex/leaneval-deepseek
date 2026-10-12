import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.LatGreen

/-- A measurable function of one variable stays measurable when the two variables of
`E × E` are mixed by the shear `(z₁, z₂) ↦ (z₁ + z₂, z₂)`.

The point is that this shear is a measure preserving transformation of
`volume.prod volume`: it is (the linear map underlying) the Mathlib lemma
`MeasureTheory.measurePreserving_add_prod`, which says that `(x, y) ↦ (x + y, y)`
preserves `μ.prod ν` for a right invariant measure `μ`.  Hence
`z ↦ V z.2 * V (z.2 + z.1)` is the composition of the (jointly) a.e. measurable map
`(u, v) ↦ V u * V v` with this measure preserving shear. -/
theorem aemeasurable_shear_mul_div {V : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hV : AEMeasurable V MeasureTheory.volume) :
    AEMeasurable (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        V z.2 * V (z.2 + z.1) / ‖z.1‖)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  -- The product of two copies of `V`, as a function on `E × E`.
  have hW : AEMeasurable
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => V p.1 * V p.2)
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    ((hV.comp_quasiMeasurePreserving MeasureTheory.Measure.quasiMeasurePreserving_fst).mul
      (hV.comp_quasiMeasurePreserving MeasureTheory.Measure.quasiMeasurePreserving_snd))
  -- The shear `(z₁, z₂) ↦ (z₁ + z₂, z₂)` preserves `volume.prod volume`.
  have hT : MeasureTheory.MeasurePreserving
      (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => (z.1 + z.2, z.2))
      (MeasureTheory.volume.prod MeasureTheory.volume)
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    MeasureTheory.measurePreserving_add_prod _ _
  -- Pulling `hW` back along the shear gives `z ↦ V (z₁ + z₂) * V z₂`.
  have h1 : AEMeasurable
      (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => V (z.1 + z.2) * V z.2)
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    hW.comp_quasiMeasurePreserving hT.quasiMeasurePreserving
  have h2 : AEMeasurable
      (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => V z.2 * V (z.2 + z.1))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    simpa only [add_comm, mul_comm] using h1
  -- Division by the continuous (hence measurable) function `z ↦ ‖z₁‖`.
  have h3 : AEMeasurable
      (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => ‖z.1‖)
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    (continuous_norm.comp continuous_fst).aemeasurable
  exact h2.div h3

end Work.BoseFixR.LatGreen
