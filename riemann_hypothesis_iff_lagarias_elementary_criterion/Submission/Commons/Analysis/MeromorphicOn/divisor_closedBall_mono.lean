import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Meromorphic.Divisor

namespace Commons.Analysis.MeromorphicOn

/--
For an entire function `f`, the divisor on a closed ball is monotone in the radius: enlarging the
ball can only increase the divisor pointwise.

Indeed, if `u` lies in the smaller ball then it lies in the larger one as well, and both divisors
evaluate to `(meromorphicOrderAt f u).untop₀`. If `u` lies outside the smaller ball, the left-hand
side is `0`, while on the larger ball the value is `(meromorphicOrderAt f u).untop₀ ≥ 0` because an
entire function has no poles (its order is everywhere non-negative).
-/
theorem divisor_closedBall_mono {f : ℂ → ℂ} (hf : Differentiable ℂ f) {R R' : ℝ} (hRR : R ≤ R')
    (u : ℂ) :
    (MeromorphicOn.divisor f (Metric.closedBall 0 R)) u ≤
      (MeromorphicOn.divisor f (Metric.closedBall 0 R')) u := by
  have hmer : ∀ (S : Set ℂ), MeromorphicOn f S := fun S x _ => (hf.analyticAt x).meromorphicAt
  by_cases hu : u ∈ Metric.closedBall (0 : ℂ) R
  · have hu' : u ∈ Metric.closedBall (0 : ℂ) R' := Metric.closedBall_subset_closedBall hRR hu
    rw [MeromorphicOn.divisor_apply (hmer _) hu, MeromorphicOn.divisor_apply (hmer _) hu']
  · have h0 : (MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) R)) u = 0 := by
      rw [MeromorphicOn.divisor_def]; simp [hu]
    rw [h0]
    by_cases hu' : u ∈ Metric.closedBall (0 : ℂ) R'
    · rw [MeromorphicOn.divisor_apply (hmer _) hu']
      exact WithTop.untop₀_nonneg.mpr (AnalyticAt.meromorphicOrderAt_nonneg (hf.analyticAt u))
    · rw [MeromorphicOn.divisor_def]; simp [hu']

end Commons.Analysis.MeromorphicOn