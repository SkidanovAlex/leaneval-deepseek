import Mathlib
import Submission.Work.WilE9G.Sard.Basic

open MeasureTheory MeasureTheory.Measure Set TopologicalSpace Module Filter
open scoped MeasureTheory ENNReal NNReal Topology

set_option linter.unusedVariables false

namespace Work.WilE9G.Sard

/-- **The low-dimensional case of Morse–Sard.**  If `n < m` the image of `ℝⁿ` under a map
analytic on an open set is Lebesgue-null, so a fortiori the critical values are null.

The proof is the Hausdorff-dimension argument: an analytic map is differentiable, a differentiable
map does not increase Hausdorff dimension, `dimH ℝⁿ = n < m`, a set of Hausdorff dimension `< m` is
`μH[m]`-null, and on `Fin m → ℝ` the measure `μH[m]` is Lebesgue measure. -/
theorem volume_image_eq_zero_of_lt {n m : ℕ} (h : n < m) (f : (Fin n → ℝ) → (Fin m → ℝ))
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hf : AnalyticOn ℝ f U) :
    MeasureTheory.volume (f '' U) = 0 := by
  -- `dimH (f '' U) ≤ n`: `f` is differentiable on `U`, hence does not increase Hausdorff dimension,
  -- and `U ⊆ ℝⁿ` has `dimH ≤ finrank ℝ (Fin n → ℝ) = n`.
  have h1 : dimH (f '' U) ≤ ((n : ℝ≥0) : ℝ≥0∞) := by
    refine hf.differentiableOn.dimH_image_le.trans ?_
    calc dimH U ≤ dimH (Set.univ : Set (Fin n → ℝ)) := dimH_mono (Set.subset_univ U)
      _ = finrank ℝ (Fin n → ℝ) := Real.dimH_univ_eq_finrank _
      _ = ((n : ℝ≥0) : ℝ≥0∞) := by simp
  -- `n < m` upgrades this to `dimH (f '' U) < m`, so `μH[m] (f '' U) = 0`.
  have h2 : dimH (f '' U) < ((m : ℝ≥0) : ℝ≥0∞) := by
    refine h1.trans_lt ?_
    exact_mod_cast h
  have h0 : (μH[(m : ℝ≥0)] : Measure (Fin m → ℝ)) (f '' U) = 0 :=
    hausdorffMeasure_of_dimH_lt h2
  -- on `Fin m → ℝ` the `m`-dimensional Hausdorff measure is Lebesgue measure.
  have hvol : (μH[(m : ℝ≥0)] : Measure (Fin m → ℝ)) = MeasureTheory.volume := by
    simpa using hausdorffMeasure_pi_real (ι := Fin m)
  rwa [hvol] at h0

end Work.WilE9G.Sard
