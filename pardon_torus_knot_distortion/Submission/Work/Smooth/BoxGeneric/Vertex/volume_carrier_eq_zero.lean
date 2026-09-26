import Mathlib
import Submission.Work.Smooth.BoxGeneric.Defs
import Submission.Work.Smooth.BoxGeneric.Vertex

/-!
# The surface `F = ψ(standard torus)` is Lebesgue-null in `ℝ³`

The carrier of `Work.Smooth.Morse.torus ψ` is the image of the parametrisation
`param ψ : ℝ × ℝ → ℝ³`, `p ↦ ψ (torusMap p)`.  It is the image of a `C¹` map whose *domain* is
two-dimensional, and such an image has Lebesgue measure zero in `ℝ³`.

The route taken here avoids any Sard-type or covering argument and instead uses the Hausdorff
dimension, which Mathlib already controls for `C¹` maps on finite-dimensional real vector spaces:

* `ContDiff.dimH_range_le` gives `dimH (range f) ≤ finrank ℝ (ℝ × ℝ) = 2`;
* hence the `3`-dimensional Hausdorff measure of the range vanishes
  (`hausdorffMeasure_of_dimH_lt`), and
* the Lebesgue measure is absolutely continuous with respect to the `d`-dimensional Hausdorff
  measure on `ℝ^d` (`Measure.absolutelyContinuous_isAddHaarMeasure`, since the former is a
  translation invariant σ-finite measure and the latter an additive Haar measure).

The second ingredient is the only place where the dimension `3` enters.
-/

open LeanEval.KnotTheory.PardonDistortion
open MeasureTheory Set
open scoped ENNReal NNReal

namespace Work.Smooth.BoxGeneric.Vertex

noncomputable section

/-- **A `C¹` image of a plane has measure zero in `ℝ³`.**

For a `C¹` map `f : ℝ × ℝ → ℝ³` the range of `f` is Lebesgue-null: the Hausdorff dimension of the
range is at most the dimension `2` of the domain, so the `3`-dimensional Hausdorff measure of the
range vanishes, and Lebesgue measure on `ℝ³` is absolutely continuous with respect to the
`3`-dimensional Hausdorff measure. -/
theorem volume_range_eq_zero_of_contDiff {f : ℝ × ℝ → R3} (hf : ContDiff ℝ 1 f) :
    MeasureTheory.volume (Set.range f) = 0 := by
  -- `f` does not increase Hausdorff dimension, and `dimH (ℝ × ℝ) = 2 < 3`.
  have hdim : dimH (Set.range f) ≤ (2 : ℝ≥0∞) := by
    have h2 := ContDiff.dimH_range_le (E := ℝ × ℝ) (F := R3) hf
    simpa using h2
  have hlt : dimH (Set.range f) < (3 : ℝ≥0) := by
    calc dimH (Set.range f) ≤ (2 : ℝ≥0∞) := hdim
      _ < ((3 : ℝ≥0) : ℝ≥0∞) := by norm_num
  -- Hence the `3`-dimensional Hausdorff measure of the range vanishes.
  have hH : (μH[((3 : ℕ) : ℝ)] : Measure R3) (Set.range f) = 0 := by
    simpa using hausdorffMeasure_of_dimH_lt hlt
  -- Lebesgue measure is absolutely continuous with respect to it.
  have hAC : (MeasureTheory.volume : Measure R3) ≪ (μH[((3 : ℕ) : ℝ)] : Measure R3) :=
    MeasureTheory.Measure.absolutelyContinuous_isAddHaarMeasure _ _
  exact hAC hH

/-- **The torus `F = ψ(standard torus)` has measure zero in `ℝ³`.** -/
theorem volume_carrier_eq_zero (ψ : Submission.Diffeo) :
    MeasureTheory.volume
      ((Work.Smooth.Morse.torus ψ).carrier : Set LeanEval.KnotTheory.PardonDistortion.R3) = 0 := by
  rw [Work.Smooth.Morse.torus_carrier]
  exact volume_range_eq_zero_of_contDiff ((Work.Smooth.Morse.param_contDiff ψ).of_le (by norm_num))

end

end Work.Smooth.BoxGeneric.Vertex
