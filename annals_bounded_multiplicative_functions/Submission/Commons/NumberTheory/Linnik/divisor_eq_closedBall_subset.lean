import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Meromorphic.Divisor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.Linnik

lemma divisor_eq_closedBall_subset {f : ℂ → ℂ} {a b : ℂ} {ra rb : ℝ} {u : ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall a ra ∪ Metric.closedBall b rb))
    (hu₁ : u ∈ Metric.closedBall a ra) (hu₂ : u ∈ Metric.closedBall b rb) :
    MeromorphicOn.divisor f (Metric.closedBall a ra) u =
      MeromorphicOn.divisor f (Metric.closedBall b rb) u := by
  -- On each closed ball, the divisor at an interior/exterior point `u ∈ ball` is the
  -- untop of the (intrinsic) meromorphic order of `f` at `u`, so both sides coincide.
  rw [MeromorphicOn.divisor_apply (hf.meromorphicOn.mono_set (Set.subset_union_left)) hu₁,
      MeromorphicOn.divisor_apply (hf.meromorphicOn.mono_set (Set.subset_union_right)) hu₂]

end Commons.NumberTheory.Linnik