/-
# Vocabulary for the weighted Hardy inequality `Work.FTS.EllipticEst.AngGap.hardy`

The weighted Hardy estimate of the angular gap-Wirtinger development,

  `12 * ∫_{Iθ} V² ≤ ∫_{Iθ} h²`,   `V = angV h = angG h / sin 2θ`,

is proved from the exact identity

  `h² - 12 V² - (h - 6 cot(2θ) V)² = (6 V² cot 2θ)'`   on `(0, π/2)`,

i.e. the integrand `F` below is the derivative of `angPhiH h`.  This file only
introduces the two abbreviations `angFt` (`(h - 6 cot 2θ V)²`) and `angF`
(the integrand `F`) so that all the pieces of the argument can name them.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.FTS.EllipticEst.AngGap.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngGap

set_option autoImplicit false

/-- The "completed square" term `(h θ - 6 cot(2θ) V θ)²`, where `V = angV h`. -/
def angFt (h : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (h θ - 6 * Real.cot (2 * θ) * angV h θ) ^ 2

/-- The integrand of the weighted Hardy identity:
`angF h θ = (h θ)² - 12 (V θ)² - (h θ - 6 cot(2θ) V θ)²`, i.e. the function whose
derivative on `(0, π/2)` is `angPhiH h = 6 V² cot 2θ`. -/
def angF (h : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (h θ) ^ 2 - 12 * (angV h θ) ^ 2 - angFt h θ

/-- The defining equation of `angF`, with `angFt` expanded: this is exactly the
integrand appearing in the statement of the Hardy inequality. -/
theorem angF_eq (h : ℝ → ℝ) (θ : ℝ) :
    angF h θ = (h θ) ^ 2 - 12 * (angV h θ) ^ 2
      - (h θ - 6 * Real.cot (2 * θ) * angV h θ) ^ 2 := rfl

/-- `angF` split as the difference of `h² - 12 V²` and `angFt`. -/
theorem angF_eq_sub (h : ℝ → ℝ) (θ : ℝ) :
    angF h θ = ((h θ) ^ 2 - 12 * (angV h θ) ^ 2) - angFt h θ := rfl

theorem angFt_nonneg (h : ℝ → ℝ) (θ : ℝ) : 0 ≤ angFt h θ := sq_nonneg _

end Work.FTS.EllipticEst.AngGap
