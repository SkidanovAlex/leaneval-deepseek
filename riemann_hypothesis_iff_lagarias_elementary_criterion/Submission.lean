import ChallengeDeps
import Submission.Helpers
import Submission.Work.RHContract.Final

open LeanEval.NumberTheory
open scoped ArithmeticFunction.sigma

namespace Submission

theorem riemann_hypothesis_iff_lagarias_elementary_criterion :
    RiemannHypothesis ↔ LagariasElementaryCriterion :=
  Work.RHContract.riemann_hypothesis_iff_lagarias_elementary_criterion

end Submission
