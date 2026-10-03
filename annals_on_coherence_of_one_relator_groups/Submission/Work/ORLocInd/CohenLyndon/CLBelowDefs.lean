/-
# The strong induction hypothesis of the Cohen--Lyndon induction

The Cohen--Lyndon basis theorem for free groups is proved by strong induction on `relatorNorm`,
*uniformly over all generating types in the universe*: the induction step replaces the generating
type `α` by a rewritten one (the decorated alphabet of the Magnus decomposition
`({a : α // a ≠ t}) × ℤ`, or the enlarged alphabet of the substitution step), so the induction
hypothesis must be available at every type.

`CLBelow N` is that hypothesis: the Cohen--Lyndon property for every relator of norm `< N` over
every generating type.  This file records it together with its elementary API (monotonicity).
-/
import Mathlib
import Submission.Work.ORLocInd.CohenLyndon.NCForm
import Submission.Work.OROneRel.HNNStep

set_option autoImplicit false
set_option linter.dupNamespace false

universe u

namespace Work.ORLocInd.CohenLyndon

/-- **The induction hypothesis of the Cohen--Lyndon theorem, uniformly over all generating
types.**  `CLBelow N` says that every relator `s` of norm `< N` which is nontrivial and not a
proper power has the Cohen--Lyndon property, over *every* generating type `γ : Type u`. -/
def CLBelow (N : ℕ) : Prop :=
  ∀ (γ : Type u) [DecidableEq γ] (s : FreeGroup γ),
    ¬ Work.OROneRel.IsProperPower s → s ≠ 1 →
    Work.OROneRel.relatorNorm s < N → Work.CohenLyndon.CohenLyndonNC s

/-- The induction hypothesis is monotone in the bound: a hypothesis below a larger bound gives one
below a smaller bound. -/
theorem CLBelow.mono {N N' : ℕ} (h : N ≤ N') (hCL : CLBelow.{u} N') : CLBelow.{u} N :=
  fun γ [DecidableEq γ] s hpp hne hlt => hCL γ s hpp hne (lt_of_lt_of_le hlt h)

end Work.ORLocInd.CohenLyndon
