import Mathlib
import Submission.Work.TMC16Core.Defs

/-!
# Definitions for the AJ §9 non-resonant uniformity (`uni_nonres_aj`)

`sepB c δ M` is the bound produced by the "separation + Stirling" argument for a sum of
`-log |sin|` over `M` points whose fractional distances are bounded below by `c` and whose
signed representatives are pairwise `δ`-separated inside each sign class (see
`Work.Basic.UniNonres.sep_sum`):

* `M ≤ 1`: there is at most one point, so the crude single-term bound `M · log (1/(2c))` is
  both valid and sharp;
* `M ≥ 2`: those `M` points split into at most two sign classes, each of which is `δ`-separated
  as a set of values; applying `cluster_single` to each class and using
  `(M₁-1)! (M₂-1)! ≥ (⌊(M-2)/2⌋!)²` for `M₁ + M₂ = M` gives
  `2 log (1/(2 min c δ)) + (M-2) log (1/(2δ)) - 2 log (⌊(M-2)/2⌋!)`.
-/

namespace Work.Basic.UniNonres

open Work.TMC16Core

/-- The separation/Stirling bound for a sum of `M` terms `-log |sin (π (ξ + k α))|` whose
fractional distances are `≥ c` and whose signed representatives are pairwise `δ`-separated
within each sign class. -/
noncomputable def sepB (c δ : ℝ) (M : ℕ) : ℝ :=
  if M ≤ 1 then (M : ℝ) * Real.log (1 / (2 * c))
  else 2 * Real.log (1 / (2 * min c δ)) + ((M : ℝ) - 2) * Real.log (1 / (2 * δ))
    - 2 * Real.log ((((M - 2) / 2).factorial : ℕ) : ℝ)

end Work.Basic.UniNonres
