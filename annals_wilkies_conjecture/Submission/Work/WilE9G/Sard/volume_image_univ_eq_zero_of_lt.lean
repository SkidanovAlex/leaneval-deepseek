import Mathlib

/-!
# The image of `ℝ^d` under a `C^1` map into `ℝ^n` with `d < n` is Lebesgue-null

This is the "trivial" extreme case of Sard's theorem: a `C^1` (indeed merely differentiable) map
from a lower-dimensional Euclidean space into a higher-dimensional one cannot have an image of
positive `n`-dimensional measure. The proof goes through Hausdorff dimension:

* a differentiable map from `Fin d → ℝ` does not increase Hausdorff dimension, so
  `dimH (f '' univ) ≤ d` (`Differentiable.dimH_range_le`);
* a set of Hausdorff dimension `< n` is null for the `n`-dimensional Hausdorff measure
  (`hausdorffMeasure_of_dimH_lt`);
* on `Fin n → ℝ`, the `n`-dimensional Hausdorff measure *is* Lebesgue measure
  (`hausdorffMeasure_pi_real`).
-/

open MeasureTheory MeasureTheory.Measure Set TopologicalSpace Module Filter
open scoped MeasureTheory ENNReal NNReal Topology

namespace Work.WilE9G.Sard

theorem volume_image_univ_eq_zero_of_lt {d n : ℕ} (h : d < n) (f : (Fin d → ℝ) → (Fin n → ℝ))
    (hf : ContDiff ℝ 1 f) : MeasureTheory.volume (f '' Set.univ) = 0 := by
  -- Differentiable maps do not increase Hausdorff dimension.
  have h1 : dimH (range f) ≤ finrank ℝ (Fin d → ℝ) :=
    Differentiable.dimH_range_le hf.differentiable_one
  -- hence the range has Hausdorff dimension at most `d`.
  have h2 : dimH (f '' Set.univ) ≤ (d : ℝ≥0∞) := by
    rw [Set.image_univ]
    simpa using h1
  -- and `d < n`, so the `n`-dimensional Hausdorff measure of the image vanishes.
  have h3 : dimH (f '' Set.univ) < ((n : ℝ≥0) : ℝ≥0∞) := by
    refine h2.trans_lt ?_
    exact_mod_cast h
  have h0 : (μH[(n : ℝ≥0)] : Measure (Fin n → ℝ)) (f '' Set.univ) = 0 :=
    hausdorffMeasure_of_dimH_lt h3
  -- on `Fin n → ℝ` the `n`-dimensional Hausdorff measure coincides with Lebesgue measure.
  have hvol : (μH[(n : ℝ≥0)] : Measure (Fin n → ℝ)) = MeasureTheory.volume := by
    have := hausdorffMeasure_pi_real (ι := Fin n)
    simpa using this
  rwa [hvol] at h0

end Work.WilE9G.Sard
