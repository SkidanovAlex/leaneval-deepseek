import Mathlib

/-!
# Small-dimensional subsets of the pair space are Lebesgue-null

A set in `ℝ^n × ℝ^n` whose Hausdorff dimension is `< 2n` is Lebesgue-null: both `volume` and the
`2n`-dimensional Hausdorff measure are additive Haar measures, hence mutually absolutely
continuous.
-/

open scoped Manifold ContDiff
open Topology MeasureTheory

namespace Work.Projection

/-- A set in the pair space `ℝ^n × ℝ^n` of Hausdorff dimension `< 2n` is Lebesgue-null. -/
theorem volume_prod_eq_zero_of_dimH_lt {n : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))} (h : dimH s < 2 * n) :
    volume s = 0 := by
  set E := EuclideanSpace ℝ (Fin n) with hE
  haveI : Measure.IsAddHaarMeasure ((volume : Measure E).prod (volume : Measure E)) :=
    Measure.prod.instIsAddHaarMeasure volume volume
  have hfin : (Module.finrank ℝ (E × E) : NNReal) = (2 * n : NNReal) := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin]
    push_cast
    ring
  haveI : Measure.IsAddHaarMeasure (μH[(2 * n : NNReal)] : Measure (E × E)) := by
    have h2 : (2 * n : NNReal) = (Module.finrank ℝ (E × E) : NNReal) := hfin.symm
    rw [h2]
    exact isAddHaarMeasure_hausdorffMeasure
  refine measure_zero_of_dimH_lt (μ := volume) (d := (2 * n : NNReal)) ?_ ?_
  · exact Measure.absolutelyContinuous_isAddHaarMeasure _ _
  · simpa using h

end Work.Projection
