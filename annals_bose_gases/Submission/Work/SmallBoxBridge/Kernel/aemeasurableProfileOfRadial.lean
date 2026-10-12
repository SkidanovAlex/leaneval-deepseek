import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A.e. measurability of the radial profile of an a.e. strongly measurable radial function

If `Φ : ℝ³ → ℝ≥0∞` is almost everywhere strongly measurable for the Lebesgue measure and is
*radial* (`Φ p = Φ q` whenever `‖p‖ = ‖q‖`), then its restriction to any ray through the
origin is almost everywhere measurable with respect to the radial measure
`Measure.volumeIoiPow 2` on `(0, ∞)` (Lebesgue measure with density `r ↦ r²`).

The mathematics is the polar-coordinate decomposition of Lebesgue measure on `ℝ³`:
`homeomorphUnitSphereProd` identifies `ℝ³ \ {0}` with `S² × (0, ∞)` and carries `volume`
to `volume.toSphere.prod (volumeIoiPow 2)`.  Since `Φ` is radial, it becomes the function
`(e, r) ↦ φ r` on the product, where `φ r = Φ (r • e₀)`.  Along the first factor the measure
`volume.toSphere` is finite and non-zero, so a.e. measurability of `(e, r) ↦ φ r` descends
to a.e. measurability of `φ` against `volumeIoiPow 2` (this is
`AEStronglyMeasurable.comp_snd_iff`).

## Main statement

`aemeasurableProfileOfRadial`
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Work.SmallBoxBridge.Kernel

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Polar-coordinate measure preservation on `ℝ³`, with the radial exponent computed
as `2` (`Module.finrank ℝ ℝ³ - 1 = 3 - 1 = 2`).  `homeomorphUnitSphereProd` is a
measure-preserving homeomorphism from `{(0)}ᶜ` (with `volume.comap Subtype.val`) onto
`S² × (0, ∞)` carrying `volume.toSphere.prod (volumeIoiPow 2)`. -/
lemma measurePreserving_homeomorphUnitSphereProd_r3 :
    MeasurePreserving (homeomorphUnitSphereProd ℝ³)
      (Measure.comap (Subtype.val : ({0}ᶜ : Set ℝ³) → ℝ³) (volume : Measure ℝ³))
      ((volume : Measure ℝ³).toSphere.prod (Measure.volumeIoiPow 2)) := by
  have h := Measure.measurePreserving_homeomorphUnitSphereProd (volume : Measure ℝ³)
  simpa using h

theorem aemeasurableProfileOfRadial
    (Φ : EuclideanSpace ℝ (Fin 3) → ENNReal)
    (hΦ : MeasureTheory.AEStronglyMeasurable Φ (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))
    (hrad : ∀ p q : EuclideanSpace ℝ (Fin 3), ‖p‖ = ‖q‖ → Φ p = Φ q) :
    AEMeasurable (fun r : Set.Ioi (0 : ℝ) => Φ ((r : ℝ) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)))
      (MeasureTheory.Measure.volumeIoiPow 2) := by
  classical
  -- `Φ` is a.e. measurable, hence so is its restriction to the punctured space `{(0)}ᶜ`.
  have hΦa : AEMeasurable Φ (volume : Measure ℝ³) := hΦ.aemeasurable
  have h₁ : AEMeasurable (fun x : ({0}ᶜ : Set ℝ³) => Φ (x : ℝ³))
      (Measure.comap (Subtype.val : ({0}ᶜ : Set ℝ³) → ℝ³) (volume : Measure ℝ³)) :=
    (aemeasurable_restrict_iff_comap_subtype (s := ({0}ᶜ : Set ℝ³))
      (measurableSet_singleton (0 : ℝ³)).compl (μ := (volume : Measure ℝ³)) (f := Φ)).mp
      (hΦa.mono_measure Measure.restrict_le_self)
  -- The inverse `h.symm : S² × (0,∞) → {(0)}ᶜ` of the polar homeomorphism pushes the product
  -- measure back to the comap measure on the punctured space.
  have hmp := measurePreserving_homeomorphUnitSphereProd_r3
  have hmap : Measure.map (⇑(homeomorphUnitSphereProd ℝ³).symm)
        ((volume : Measure ℝ³).toSphere.prod (Measure.volumeIoiPow 2))
      = Measure.comap (Subtype.val : ({0}ᶜ : Set ℝ³) → ℝ³) (volume : Measure ℝ³) := by
    rw [← hmp.map_eq,
      Measure.map_map (Homeomorph.measurableEmbedding _).measurable hmp.measurable,
      Homeomorph.symm_comp_self, Measure.map_id]
  -- Transport a.e. measurability across the measure-preserving homeomorphism.
  have h₂ : AEMeasurable (fun y : Metric.sphere (0 : ℝ³) 1 × Set.Ioi (0 : ℝ) =>
        Φ (((homeomorphUnitSphereProd ℝ³).symm y : ({0}ᶜ : Set ℝ³)) : ℝ³))
      ((volume : Measure ℝ³).toSphere.prod (Measure.volumeIoiPow 2)) := by
    have key : AEMeasurable (fun x : ({0}ᶜ : Set ℝ³) => Φ (x : ℝ³))
        (Measure.map (⇑(homeomorphUnitSphereProd ℝ³).symm)
          ((volume : Measure ℝ³).toSphere.prod (Measure.volumeIoiPow 2))) := by
      rw [hmap]; exact h₁
    exact (MeasurableEmbedding.aemeasurable_map_iff
      (Homeomorph.measurableEmbedding (homeomorphUnitSphereProd ℝ³).symm)).mp key
  -- Radiality: the profile depends only on the second coordinate `r`.
  have h₃ : AEMeasurable (fun y : Metric.sphere (0 : ℝ³) 1 × Set.Ioi (0 : ℝ) =>
        Φ ((y.2 : ℝ) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)))
      ((volume : Measure ℝ³).toSphere.prod (Measure.volumeIoiPow 2)) := by
    refine h₂.congr (Filter.Eventually.of_forall fun y => ?_)
    show Φ (((homeomorphUnitSphereProd ℝ³).symm y : ({0}ᶜ : Set ℝ³)) : ℝ³)
        = Φ ((y.2 : ℝ) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ))
    rw [homeomorphUnitSphereProd_symm_apply_coe]
    apply hrad
    rw [norm_smul, norm_smul,
      show ‖(y.1 : ℝ³)‖ = 1 from by simpa only [Metric.mem_sphere, dist_zero_right] using y.1.2]
    simp
  -- Descend along the second coordinate: `volume.toSphere` is a finite non-zero measure.
  have hσ : (volume : Measure ℝ³).toSphere ≠ 0 := Measure.toSphere_ne_zero _
  have h₄ : AEStronglyMeasurable
      (fun r : Set.Ioi (0 : ℝ) => Φ ((r : ℝ) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)))
      (Measure.volumeIoiPow 2) :=
    (AEStronglyMeasurable.comp_snd_iff (μ := (volume : Measure ℝ³).toSphere)
      (ν := Measure.volumeIoiPow 2) hσ).mp
      (aestronglyMeasurable_iff_aemeasurable.mpr h₃)
  exact h₄.aemeasurable

end Work.SmallBoxBridge.Kernel
