import Mathlib
import Submission.Work.C17I.defs

namespace Work.C17I

/-- The rational coefficient `logPCoeffQ` is the cast of `logPCoeff` up to the
`ℤ`-relation defect `r_a·η_a + r_b·η_b + r_ab·η_aη_b − r_0` (cf. `logPCoeff_eq_rat`,
which is the special case of this identity under the relation `= 0`). -/
theorem logPCoeffQ_diff (a b : ℚ) (ra rb rab r0 : ℤ) (n : ℕ) :
    ((Submission.CDT.logPCoeffQ a b ra rb rab r0 n : ℚ) : ℝ)
      = Submission.CDT.logPCoeff (a : ℝ) (b : ℝ) ra rb rab n
        + ((ra : ℝ) * Submission.CDT.beukersEta (a : ℝ)
            + (rb : ℝ) * Submission.CDT.beukersEta (b : ℝ)
            + (rab : ℝ) * (Submission.CDT.beukersEta (a : ℝ) * Submission.CDT.beukersEta (b : ℝ))
            - (r0 : ℝ)) * (Submission.CDT.beukersUR (a : ℝ) n * Submission.CDT.beukersUR (b : ℝ) n) := by
  unfold Submission.CDT.logPCoeff Submission.CDT.logPCoeffQ Submission.CDT.beukersPaCoeff
    Submission.CDT.beukersPbCoeff Submission.CDT.beukersPabCoeff Submission.CDT.beukersD
  rw [Submission.CDT.beukersUR_eq_cast a n, Submission.CDT.beukersVR_eq_cast a n,
      Submission.CDT.beukersUR_eq_cast b n, Submission.CDT.beukersVR_eq_cast b n]
  push_cast
  ring

end Work.C17I
