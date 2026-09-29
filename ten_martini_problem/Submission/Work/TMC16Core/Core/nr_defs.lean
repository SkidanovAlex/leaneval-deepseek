import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Core.geom

/-! # Definition of the non-resonant uniformity rate (AJ §9.4, small-`s` regime). -/

namespace Work.TMC16Core.Core

open Work.TMC16Core

noncomputable section

/-- The uniformity rate of the non-resonant two-window family of `Core.geom` in AJ's
small-`s` regime (`2 s q(n-1) ≤ q n`).  Up to the absolute constants it is
`2 log(q n/s)/q(n-1)`, which is `≤ (2/9) b₀ + o(1) < L/8 < 3L/16` under the non-resonance
`q n^{8/9} ≤ s q(n-1)` and `DiophBelow α b₀`. -/
def rateNR (q : ℕ → ℕ) (n s : ℕ) (c : ℝ) : ℝ :=
  2 * Real.log (2 + (q n : ℝ) / (s : ℝ)) / (q (n - 1) : ℝ)
  + 200 * Real.log ((q (n - 1) : ℝ) + 2) / (q (n - 1) : ℝ)
  + 2 * Real.log (2 + 1 / c) / ((s : ℝ) * (q (n - 1) : ℝ))
  + 400 / (q (n - 1) : ℝ)

end

end Work.TMC16Core.Core
