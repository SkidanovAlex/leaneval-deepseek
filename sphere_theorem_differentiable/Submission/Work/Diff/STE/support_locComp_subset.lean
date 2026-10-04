import Mathlib
import Submission.Work.Diff.STE.ChartComp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The support of a localised chart component lies in the chart ball

The localised component `locComp θ x₀ g i a b` vanishes outside the support of the partition
function `θ i`, which is contained in `U i`; hence its support is inside `U i`.  This is the
localisation step `B2` of the STE design (it makes the periodisation of the component legitimate).
-/

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.STE

theorem support_locComp_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    {ι₀ : Type*} (θ : SmoothPartitionOfUnity ι₀ I M) (x₀ : ι₀ → M)
    (U : ι₀ → Set M) (hsub : θ.IsSubordinate U)
    (r : ι₀ → ℝ)
    (hU : ∀ i, U i ⊆ (extChartAt I (x₀ i)) ⁻¹'
      Metric.ball ((extChartAt I (x₀ i)) (x₀ i)) (r i))
    (g : Submission.Diff.SMet I M) (i : ι₀) (a b : Fin (Module.finrank ℝ E)) :
    ∀ y : E, y ∈ (extChartAt I (x₀ i)).target →
      Work.Diff.STE.locComp θ x₀ g i a b y ≠ 0 →
      y ∈ Metric.ball ((extChartAt I (x₀ i)) (x₀ i)) (r i) := by
  intro y hy hne
  -- the product is non-zero, so the first factor is non-zero
  have hθ : θ i ((extChartAt I (x₀ i)).symm y) ≠ 0 := by
    intro h0
    exact hne (by simp only [locComp]; rw [h0, zero_mul])
  -- hence the point lies in the closure of the support of `θ i`, which is inside `U i`
  have hz : (extChartAt I (x₀ i)).symm y ∈ U i :=
    hsub i (subset_tsupport (θ i) (Function.mem_support.mpr hθ))
  -- finally read the ball condition back through the chart
  have h2 := hU i hz
  simp only [Set.mem_preimage] at h2
  rwa [PartialEquiv.right_inv (extChartAt I (x₀ i)) hy] at h2

end Work.Diff.STE
