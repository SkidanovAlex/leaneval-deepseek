import Mathlib
import Submission.Work.Tower.APDensity.Basic

namespace Work.Tower.APDensity.Analytic

theorem lambdaOne_tsum_split {δ : ℝ} (hδ : 0 < δ) :
    ∑' n : ℕ, Work.Tower.LambdaOne n / (n : ℝ) ^ (1 + δ) =
      (∑' n : ℕ, (if n.Prime then Work.Tower.LambdaOne n else 0) / (n : ℝ) ^ (1 + δ))
      + ∑' n : ℕ, (if n.Prime then 0 else Work.Tower.LambdaOne n) / (n : ℝ) ^ (1 + δ) := by
  have h1 : 1 < 1 + δ := by linarith
  rw [← Summable.tsum_add (Work.Tower.summable_primePart_div_rpow h1)
    (Work.Tower.summable_nonprimePart_div_rpow h1)]
  refine tsum_congr fun n => ?_
  by_cases hp : n.Prime <;> simp [hp]

end Work.Tower.APDensity.Analytic
