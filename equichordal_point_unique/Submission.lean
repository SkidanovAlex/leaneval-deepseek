import ChallengeDeps
import Submission.Helpers
import Submission.Work.EQ.Final

open LeanEval.Geometry.Equichordal
open Metric Set

namespace Submission

theorem equichordal_point_unique {K : Set Plane}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : (interior K).Nonempty) :
    ¬ ∃ P Q : Plane,
      P ≠ Q ∧ IsEquichordalPoint K P ∧ IsEquichordalPoint K Q :=
  Work.EQ.equichordal_main hK hconv hne

end Submission
