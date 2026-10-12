import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Submission.Work.TrialState.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.TrialState.Basic

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

theorem contDiff_trial {N : ℕ} {φ f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (Work.TrialState.trial N φ f) := by
  unfold Work.TrialState.trial
  fun_prop

end Work.TrialState.Basic
