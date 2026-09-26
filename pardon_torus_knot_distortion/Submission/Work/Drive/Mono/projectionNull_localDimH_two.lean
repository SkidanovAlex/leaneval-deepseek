import Mathlib
import Submission.Work.Projection.dimH_image_le_of_contDiffOn

/-!
# A `C¹`-parametrised two-dimensional set projects to a Lebesgue-null set of `ℝ³`

`Work.Drive.Mono.projectionNull_localDimH_two`: a subset `W` of `ℝ⁷ ≈ ℝ³ × ℝ² × ℝ²` which is
*locally* contained in the image of a `C¹` map `φ : ℝ × ℝ → ℝ⁷` has first-three-coordinates
projection of three-dimensional Lebesgue measure zero.

The proof neither needs Sard's theorem nor any regularity of `W`:

* at each `w ∈ W` the hypothesis exhibits a neighbourhood `O` of `w` with `W ∩ O ⊆ φ '' V`,
  `V` open, `φ` of class `C¹` on `V`;
* since the ambient space is second countable (`TopologicalSpace.isOpen_iUnion_countable`)
  countably many of those neighbourhoods already cover `W`;
* for a single piece, the composite `π ∘ φ` of `φ` with the linear projection `π` onto the first
  three coordinates is again `C¹` on `V`, so it does not increase Hausdorff dimension
  (`Work.Projection.dimH_image_le_of_contDiffOn`) and

  `dimH ((π ∘ φ) '' V) ≤ finrank ℝ (ℝ × ℝ) = 2 < 3 = finrank ℝ (ℝ × ℝ × ℝ)`;

* hence `μH[3] ((π ∘ φ) '' V) = 0` (`hausdorffMeasure_of_dimH_lt`) and three-dimensional
  Lebesgue measure is absolutely continuous with respect to `μH[3]`
  (`MeasureTheory.Measure.absolutelyContinuous_isAddHaarMeasure`);
* finally a countable union of null sets is null (`MeasureTheory.measure_iUnion_null`) and a subset
  of a null set is null (`MeasureTheory.measure_mono_null`).

This is the same Hausdorff-dimension technique as the sibling files
`Work.Drive.Mono.volume_image_curve_eq_zero` and
`Work.Drive.Mono.volume_image_lipschitzOnWith_real_eq_zero`.
-/

namespace Work.Drive.Mono

open MeasureTheory Set
open scoped ENNReal NNReal

set_option linter.style.haveILetI false

/-- **A `C¹` image of an open subset of `ℝ²` projects to a null set of `ℝ³`.**

If `φ : ℝ × ℝ → ℝ × ℝ × ℝ × (ℝ × ℝ) × (ℝ × ℝ)` is `C¹` on an open set `V`, then the image of
`V` under the projection onto the first three coordinates has three-dimensional Lebesgue measure
zero. -/
lemma volume_image_proj_image_eq_zero {V : Set (ℝ × ℝ)}
    {φ : ℝ × ℝ → (ℝ × ℝ × ℝ × (ℝ × ℝ) × (ℝ × ℝ))}
    (hV : IsOpen V) (hφ : ContDiffOn ℝ 1 φ V) :
    (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ × ℝ))
      ((fun w : ℝ × ℝ × ℝ × (ℝ × ℝ) × (ℝ × ℝ) => (w.1, w.2.1, w.2.2.1)) '' (φ '' V)) = 0 := by
  rw [Set.image_image]
  -- `volume` on `ℝ × ℝ × ℝ` is a product of Haar measures, hence a Haar measure.
  haveI hvol : Measure.IsAddHaarMeasure (MeasureTheory.volume : Measure (ℝ × ℝ × ℝ)) :=
    Measure.prod.instIsAddHaarMeasure (MeasureTheory.volume : Measure ℝ)
      (MeasureTheory.volume : Measure (ℝ × ℝ))
  -- the projection is smooth, so the composite with `φ` is `C¹` on `V`
  have hproj : ContDiff ℝ 1
      (fun w : ℝ × ℝ × ℝ × (ℝ × ℝ) × (ℝ × ℝ) => (w.1, w.2.1, w.2.2.1)) := by fun_prop
  have hcomp : ContDiffOn ℝ 1
      ((fun w : ℝ × ℝ × ℝ × (ℝ × ℝ) × (ℝ × ℝ) => (w.1, w.2.1, w.2.2.1)) ∘ φ) V :=
    hproj.comp_contDiffOn hφ
  -- a `C¹` map on an open set does not increase Hausdorff dimension; the source has dimension `2`
  have hdim : dimH
      (((fun w : ℝ × ℝ × ℝ × (ℝ × ℝ) × (ℝ × ℝ) => (w.1, w.2.1, w.2.2.1)) ∘ φ) '' V)
      ≤ (2 : ℝ≥0∞) := by
    have h := Work.Projection.dimH_image_le_of_contDiffOn (U := V) hV hcomp (subset_refl V)
    simpa [Module.finrank_prod, Module.finrank_self] using h
  -- which is strictly smaller than the dimension `3` of the target
  have hlt : dimH
      (((fun w : ℝ × ℝ × ℝ × (ℝ × ℝ) × (ℝ × ℝ) => (w.1, w.2.1, w.2.2.1)) ∘ φ) '' V)
      < ((((Module.finrank ℝ (ℝ × ℝ × ℝ)) : ℕ) : ℝ≥0) : ℝ≥0∞) := by
    refine lt_of_le_of_lt hdim ?_
    norm_num [Module.finrank_prod, Module.finrank_self]
  -- hence the `3`-dimensional Hausdorff measure of the image vanishes
  have hH : (μH[(Module.finrank ℝ (ℝ × ℝ × ℝ))] : Measure (ℝ × ℝ × ℝ))
      (((fun w : ℝ × ℝ × ℝ × (ℝ × ℝ) × (ℝ × ℝ) => (w.1, w.2.1, w.2.2.1)) ∘ φ) '' V) = 0 :=
    hausdorffMeasure_of_dimH_lt (d := ((Module.finrank ℝ (ℝ × ℝ × ℝ) : ℕ) : ℝ≥0)) hlt
  -- and Lebesgue measure on `ℝ³` is absolutely continuous with respect to it
  have hAC : (MeasureTheory.volume : Measure (ℝ × ℝ × ℝ)) ≪
      (μH[(Module.finrank ℝ (ℝ × ℝ × ℝ))] : Measure (ℝ × ℝ × ℝ)) :=
    MeasureTheory.Measure.absolutelyContinuous_isAddHaarMeasure _ _
  exact hAC hH

/-- **`Work.Drive.Mono.projectionNull_localDimH_two`.** A set `W ⊆ ℝ³ × ℝ² × ℝ²` which is locally
contained in the image of a `C¹` map from `ℝ × ℝ` has first-three-coordinates projection of
three-dimensional Lebesgue measure zero. -/
theorem projectionNull_localDimH_two {W : Set (ℝ × ℝ × ℝ × (ℝ × ℝ) × (ℝ × ℝ))}
    (h : ∀ w ∈ W, ∃ (O : Set (ℝ × ℝ × ℝ × (ℝ × ℝ) × (ℝ × ℝ))) (V : Set (ℝ × ℝ))
        (φ : ℝ × ℝ → (ℝ × ℝ × ℝ × (ℝ × ℝ) × (ℝ × ℝ))),
      IsOpen O ∧ w ∈ O ∧ IsOpen V ∧ ContDiffOn ℝ 1 φ V ∧ W ∩ O ⊆ φ '' V) :
    (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ × ℝ))
      ((fun w : ℝ × ℝ × ℝ × (ℝ × ℝ) × (ℝ × ℝ) => (w.1, w.2.1, w.2.2.1)) '' W) = 0 := by
  classical
  -- choose a local `C¹` chart at every point of `W`
  have hx : ∀ x : W, ∃ (O : Set (ℝ × ℝ × ℝ × (ℝ × ℝ) × (ℝ × ℝ))) (V : Set (ℝ × ℝ))
      (φ : ℝ × ℝ → (ℝ × ℝ × ℝ × (ℝ × ℝ) × (ℝ × ℝ))),
      IsOpen O ∧ x.1 ∈ O ∧ IsOpen V ∧ ContDiffOn ℝ 1 φ V ∧ W ∩ O ⊆ φ '' V :=
    fun x => h x.1 x.2
  choose O V φ hspec using hx
  have hO : ∀ x : W, IsOpen (O x) := fun x => (hspec x).1
  have hmem : ∀ x : W, x.1 ∈ O x := fun x => (hspec x).2.1
  have hV : ∀ x : W, IsOpen (V x) := fun x => (hspec x).2.2.1
  have hφ : ∀ x : W, ContDiffOn ℝ 1 (φ x) (V x) := fun x => (hspec x).2.2.2.1
  have hsub : ∀ x : W, W ∩ O x ⊆ φ x '' V x := fun x => (hspec x).2.2.2.2
  -- the chosen neighbourhoods cover `W`, and second countability extracts a countable subcover
  have hcover : W ⊆ ⋃ x : W, O x := fun _ hy => mem_iUnion.2 ⟨⟨_, hy⟩, hmem ⟨_, hy⟩⟩
  obtain ⟨t, htc, ht⟩ := TopologicalSpace.isOpen_iUnion_countable (fun x : W => O x) (fun x => hO x)
  -- so the projection of `W` is contained in a countable union of null sets
  have hsub' : (fun w : ℝ × ℝ × ℝ × (ℝ × ℝ) × (ℝ × ℝ) => (w.1, w.2.1, w.2.2.1)) '' W ⊆
      ⋃ x : t, (fun w : ℝ × ℝ × ℝ × (ℝ × ℝ) × (ℝ × ℝ) => (w.1, w.2.1, w.2.2.1)) ''
        (φ x.1 '' V x.1) := by
    rintro z ⟨y, hyW, rfl⟩
    have hy : y ∈ ⋃ x : W, O x := hcover hyW
    rw [← ht] at hy
    rcases mem_iUnion.1 hy with ⟨x, hyx⟩
    rcases mem_iUnion.1 hyx with ⟨hxt, hyx⟩
    exact mem_iUnion.2 ⟨⟨x, hxt⟩, y, hsub x ⟨hyW, hyx⟩, rfl⟩
  have hnull : (MeasureTheory.volume : Measure (ℝ × ℝ × ℝ))
      (⋃ x : t, (fun w : ℝ × ℝ × ℝ × (ℝ × ℝ) × (ℝ × ℝ) => (w.1, w.2.1, w.2.2.1)) ''
        (φ x.1 '' V x.1)) = 0 := by
    haveI : Countable t := htc.to_subtype
    exact measure_iUnion_null fun x : t => volume_image_proj_image_eq_zero (hV x.1) (hφ x.1)
  exact measure_mono_null hsub' hnull

end Work.Drive.Mono
