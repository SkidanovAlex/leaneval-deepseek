import Mathlib
import Submission.Work.Haupt.thetaCore
import Submission.Work.Haupt.pentagonal_analytic
import Submission.Work.Haupt.jtp_at_pentagonal

/-!
# The theta series at `(X^3, -X)` is Euler's pentagonal product

For `‖X‖ < 1`,

`ThetaSum (X^3) (-X) = ∏' m, (1 - X ^ (2 * m + 2))`.

The left side is, by definition, the two-sided theta series `∑' n : ℤ, (X^3)^{n^2} (-X)^n`,
which is `jtpTheta (X^3) (-X)`; `Work.Haupt.jtp_at_pentagonal` identifies that with the
pentagonal product `∏' n, (1 - X ^ (2 * (n + 1)))`.  Reindexing `n + 1 = m + 1` gives the
product in the requested normalisation.
-/

namespace Work.Haupt

/-- `jtpTheta` and `ThetaSum` are the same two-sided theta series (they have the same
defining body). -/
theorem ThetaSum_eq_jtpTheta : ThetaSum = jtpTheta := rfl

theorem ThetaSum_pentagonal (X : ℂ) (hX : ‖X‖ < 1) :
    ThetaSum (X ^ 3) (-X) = ∏' m : ℕ, (1 - X ^ (2 * m + 2)) := by
  have h := (jtp_at_pentagonal X hX).2
  rw [ThetaSum_eq_jtpTheta, h]
  exact tprod_congr (fun m => by rw [show 2 * (m + 1) = 2 * m + 2 by ring])

end Work.Haupt
