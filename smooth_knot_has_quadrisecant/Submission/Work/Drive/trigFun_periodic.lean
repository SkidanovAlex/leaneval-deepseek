import Mathlib
import Submission.Work.Drive.trigFun

namespace Work.Drive

/-- Every trigonometric sum with integer frequencies is `2 * Real.pi`-periodic.
Route: `Real.cos_add_int_mul_two_pi` and `Real.sin_add_int_mul_two_pi` termwise inside the
`Finsupp.sum`, with `Finsupp.sum_congr`. -/
theorem trigFun_periodic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Work.Drive.TrigFun E) (t : ℝ) :
    P.toFun (t + 2 * Real.pi) = P.toFun t := by
  simp only [TrigFun.toFun]
  congr 1
  · refine Finsupp.sum_congr (fun k _ => ?_)
    have hk : (k : ℝ) * (t + 2 * Real.pi) = (k : ℝ) * t + ↑k * (2 * Real.pi) := by ring
    rw [hk, Real.cos_add_int_mul_two_pi]
  · refine Finsupp.sum_congr (fun k _ => ?_)
    have hk : (k : ℝ) * (t + 2 * Real.pi) = (k : ℝ) * t + ↑k * (2 * Real.pi) := by ring
    rw [hk, Real.sin_add_int_mul_two_pi]

end Work.Drive
