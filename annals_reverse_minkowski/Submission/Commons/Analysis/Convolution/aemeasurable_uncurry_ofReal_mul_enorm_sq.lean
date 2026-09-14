import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

namespace Commons.Analysis.Convolution

open MeasureTheory
open scoped ENNReal

/-- **The difference map of a translation invariant measure is absolutely continuous.**

For a measure `volume` on a normed additive group which is invariant under right translations
(e.g. Lebesgue measure on `ℝⁿ`), the pushforward of the product measure `volume.prod volume`
under the difference map `(x, y) ↦ x - y` is absolutely continuous with respect to `volume`.
Equivalently: the preimage of a `volume`-null set under the difference map is
`volume.prod volume`-null.

This is the measure-theoretic input needed to compose an a.e.-measurable function with the
difference map appearing in convolutions and in the "commutator" expressions
`x ↦ u (x - y) - u x`. -/
theorem map_sub_prod_absolutelyContinuous {E : Type*} [NormedAddCommGroup E]
    [MeasureSpace E] [BorelSpace E] [MeasurableSub₂ E] [SFinite (volume : Measure E)]
    [(volume : Measure E).IsAddRightInvariant] :
    (Measure.map (fun p : E × E => p.1 - p.2) (volume.prod (volume : Measure E))) ≪
      (volume : Measure E) := by
  -- It suffices to check measurable `volume`-null sets `N`, then pass to `toMeasurable`.
  intro s hs
  set N := toMeasurable (volume : Measure E) s with hN
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hsub : s ⊆ N := subset_toMeasurable _ _
  have hN0 : (volume : Measure E) N = 0 := by
    rw [hN, measure_toMeasurable]; exact hs
  have hT : Measurable (fun p : E × E => p.1 - p.2) := measurable_fst.sub measurable_snd
  have hNmap : (Measure.map (fun p : E × E => p.1 - p.2) (volume.prod (volume : Measure E))) N = 0 := by
    rw [Measure.map_apply hT hNm]
    -- Tonelli: compute the measure of the preimage by integrating the measures of the slices.
    rw [Measure.prod_apply_symm (hT hNm)]
    have : ∀ y : E, (volume : Measure E) ((fun x => (x, y)) ⁻¹' (fun p : E × E => p.1 - p.2) ⁻¹' N) = 0 := by
      intro y
      -- each slice `{x | x - y ∈ N}` is a translate of `N`, hence null.
      have hmap : Measure.map (fun x : E => x - y) (volume : Measure E) = volume := by
        have : (fun x : E => x - y) = (fun x => x + (-y)) := by funext x; simp [sub_eq_add_neg]
        rw [this, map_add_right_eq_self volume (-y)]
      have hslice : (fun x : E => x - y) ⁻¹' N =
          (fun x => (x, y)) ⁻¹' (fun p : E × E => p.1 - p.2) ⁻¹' N := rfl
      rw [← hslice]
      rw [Measure.measure_preimage_of_map_eq_self hmap hNm.nullMeasurableSet]
      exact hN0
    simp only [this, lintegral_zero]
  have h := calc (Measure.map (fun p : E × E => p.1 - p.2) (volume.prod (volume : Measure E))) s
      ≤ (Measure.map (fun p : E × E => p.1 - p.2) (volume.prod (volume : Measure E))) N :=
        measure_mono hsub
    _ = 0 := hNmap
  exact le_bot_iff.mp h

theorem aemeasurable_uncurry_ofReal_mul_enorm_sq {n : ℕ}
    {ρ : EuclideanSpace ℝ (Fin n) → ℝ} (hρi : MeasureTheory.Integrable ρ MeasureTheory.volume)
    (u : EuclideanSpace ℝ (Fin n) → ℂ)
    (hu : MeasureTheory.MemLp u 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) :
    AEMeasurable (Function.uncurry fun x y : EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (ρ y) * ‖u (x - y) - u x‖ₑ ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).prod
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) := by
  have hρa : AEMeasurable ρ (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hρi.aestronglyMeasurable.aemeasurable
  have hua : AEMeasurable u (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hu.aestronglyMeasurable.aemeasurable
  -- first factor: `(x, y) ↦ ENNReal.ofReal (ρ y)`
  have h1 : AEMeasurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (ρ p.2))
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).prod
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hρa.comp_snd
  have hT : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => p.1 - p.2) :=
    measurable_fst.sub measurable_snd
  -- `u` is a.e.-measurable for the pushforward along the difference map, since that
  -- pushforward is absolutely continuous with respect to `volume`.
  have hsurj : AEMeasurable u
      (((volume : Measure (EuclideanSpace ℝ (Fin n))).prod
        (volume : Measure (EuclideanSpace ℝ (Fin n)))).map
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => p.1 - p.2)) :=
    hua.mono' (map_sub_prod_absolutelyContinuous (E := EuclideanSpace ℝ (Fin n)))
  have h2 : AEMeasurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => u (p.1 - p.2))
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).prod
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) :=
    hsurj.comp_aemeasurable' hT.aemeasurable
  have h3 : AEMeasurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => u p.1)
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).prod
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) :=
    hua.comp_fst
  -- second factor: `(x, y) ↦ ‖u (x - y) - u x‖ₑ ^ 2`
  have h5 : AEMeasurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ‖u (p.1 - p.2) - u p.1‖ₑ)
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).prod
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) := (h2.sub h3).enorm
  have h6 : AEMeasurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ‖u (p.1 - p.2) - u p.1‖ₑ ^ 2)
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).prod
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) := h5.pow_const 2
  have h7 : AEMeasurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (ρ p.2) * ‖u (p.1 - p.2) - u p.1‖ₑ ^ 2)
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).prod
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) := h1.mul h6
  exact h7

end Commons.Analysis.Convolution