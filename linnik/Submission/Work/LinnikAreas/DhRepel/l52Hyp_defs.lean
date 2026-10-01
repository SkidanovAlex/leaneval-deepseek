/-
# Vocabulary for the `L52Hyp` supply (Heath-Brown Lemma 3.1 in window form)

This file fixes the two divisor sums used by the proof of
`Work.LinnikAreas.DhRepel.l52Hyp_supply`:

* `winSum χ s δ` is (verbatim) the windowed divisor sum appearing in
  `Commons.NumberTheory.Linnik.L52Hyp`, i.e. the sum over the zeros `u` of
  `completedLFunction χ` inside the ball of radius `|s.im| + 2` that lie within distance
  `δ` of `1 + i·Im s`, of `mult u · Re (1/(s-u))`;
* `kernSum χ s R` is the *truncated symmetric partial-fraction sum*
  `Σ_{|u| ≤ R} mult u · (Re (1/(s-u)) + Re (1/(conj s + u - 1)))`,
  whose limit as `R → ∞` is `2 Re (Λ'/Λ)(s) + log N` (this is the Hadamard partial-fraction
  identity based at `s` and at `1 - conj s`, combined with the functional equation).
-/
import Mathlib
import Submission.Work.LinnikAreas.DhRepel.Defs
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi
import Submission.Commons.NumberTheory.DirichletCharacter.logDeriv_completedLFunction_conj

open Complex DirichletCharacter Metric Filter
open scoped Real Topology BigOperators
noncomputable section

namespace Work.LinnikAreas.DhRepel

/-- The windowed divisor sum of `Commons.NumberTheory.Linnik.L52Hyp`, as a standalone function. -/
def winSum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) (δ : ℝ) : ℝ :=
  ∑ᶠ u : ℂ, ((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
    (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then ((1/(s-u)).re) else 0)

/-- The truncated symmetric partial-fraction sum of the completed `L`-function. -/
def kernSum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) (R : ℝ) : ℝ :=
  ∑ᶠ u : ℂ, ((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) *
    ((1/(s-u)).re + (1/((starRingEnd ℂ) s + u - 1)).re)

/-- The first half of `kernSum` (the part whose summands are manifestly nonnegative). -/
def firstSum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) (R : ℝ) : ℝ :=
  ∑ᶠ u : ℂ, ((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) *
    (1/(s-u)).re

/-- The second half of `kernSum`. -/
def secondSum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) (R : ℝ) : ℝ :=
  ∑ᶠ u : ℂ, ((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) *
    (1/((starRingEnd ℂ) s + u - 1)).re

end Work.LinnikAreas.DhRepel
