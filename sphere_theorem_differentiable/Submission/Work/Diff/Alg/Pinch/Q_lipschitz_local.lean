import Mathlib
import Submission.Work.Diff.Alg.Pinch.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Local Lipschitz continuity of Hamilton's reaction term `Q`

The map `R ↦ Q R` of `Submission.Diff.Alg.Q` is a quadratic polynomial in the components of `R`,
hence smooth; on a ball of radius `M` its Fréchet derivative is bounded (compactness of the ball),
so `Q` is Lipschitz there with a constant depending only on `n` and `M`.

This is the `Q_lipschitz_local` estimate used to show that the ODE `R' = Q(R)` is locally
well-posed, so that Hamilton's maximum principle (and hence the invariance of the pinching set)
may be applied fibrewise.
-/

namespace Work.Diff.Alg.Pinch

open Submission.Diff.Alg

/-- Hamilton's reaction term `Q` is smooth: it is a quadratic polynomial in the components of `R`. -/
lemma contDiff_Q (n : ℕ) :
    ContDiff ℝ ⊤ (fun R : Curv4 n => Submission.Diff.Alg.Q R) := by
  unfold Submission.Diff.Alg.Q
  fun_prop

/-- `Q` is locally Lipschitz: there is a constant `C` with `‖Q R - Q S‖ ≤ C * ‖R - S‖` for all
`R, S` in the ball of radius `M`. -/
theorem Q_lipschitz_local (n : ℕ) (M : ℝ) :
    ∃ C : ℝ, ∀ R S : Submission.Diff.Alg.Curv4 n, ‖R‖ ≤ M → ‖S‖ ≤ M →
      ‖Submission.Diff.Alg.Q R - Submission.Diff.Alg.Q S‖ ≤ C * ‖R - S‖ := by
  have hQ : ContDiff ℝ ⊤ (fun R : Curv4 n => Submission.Diff.Alg.Q R) := contDiff_Q n
  -- the derivative of `Q` is continuous, hence bounded on the compact ball of radius `M`
  have hcont : Continuous (fderiv ℝ (fun R : Curv4 n => Submission.Diff.Alg.Q R)) :=
    hQ.continuous_fderiv (by simp)
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (0 : Curv4 n) M).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨C, ?_⟩
  intro R S hR hS
  have hdiff : Differentiable ℝ (fun R : Curv4 n => Submission.Diff.Alg.Q R) :=
    ContDiff.differentiable hQ (by simp)
  have hR' : R ∈ Metric.closedBall (0 : Curv4 n) M := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hR
  have hS' : S ∈ Metric.closedBall (0 : Curv4 n) M := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hS
  -- mean value inequality on the convex ball `{‖·‖ ≤ M}`
  have hder : ∀ x ∈ Metric.closedBall (0 : Curv4 n) M,
      HasFDerivWithinAt (fun R : Curv4 n => Submission.Diff.Alg.Q R)
        (fderiv ℝ (fun R : Curv4 n => Submission.Diff.Alg.Q R) x)
        (Metric.closedBall (0 : Curv4 n) M) x :=
    fun x _ => (hdiff x).hasFDerivAt.hasFDerivWithinAt
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun R : Curv4 n => Submission.Diff.Alg.Q R)
    hder hC (convex_closedBall _ _) hS' hR'

end Work.Diff.Alg.Pinch
