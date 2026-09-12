import ChallengeDeps
import Submission.Helpers
import Submission.Rad.EnfloLeRad
import Submission.Rad.TeLe

open RademacherEnfloType
open Function MeasureTheory ProbabilityTheory Measure NNReal
open scoped ENNReal

set_option autoImplicit false
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

namespace Submission

/--
Statement of Theorem 1.1 of Ivanisvili--van Handel--Volberg (Annals of Math 192 (2020)):

For any `p ∈ [1,2]`, and Banach space `X`,
`TRₚ(X) ≤ TEₚ(X) ≤ (π / √2) TRₚ(X)`.
-/
theorem theorem_1_1 (p : ℝ) (h1p : 1 ≤ p) (hp2 : p ≤ 2) :
    TR X p ≤ TE X p ∧ TE X p ≤ (pi / sqrt 2) * TR X p := by
  constructor
  · exact RadType.TR_le_TE (X := X) p
  · exact RadType.TE_le_rad_mul (X := X) p h1p hp2

end Submission
