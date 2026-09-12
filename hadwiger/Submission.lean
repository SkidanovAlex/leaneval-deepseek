import ChallengeDeps
import Submission.Helpers
import Submission.Assembly

open LeanEval.ConvexGeometry
open scoped Classical

namespace Submission

theorem hadwiger (n : ℕ) : Module.finrank ℝ (valuations n) = n + 1 :=
  hadwiger_assembly n

end Submission
