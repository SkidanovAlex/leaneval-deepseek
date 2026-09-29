import Mathlib
import Submission.Work.C7.assemble

/-!
# Area C7 — Lemma `seven` (`Submission.CDTPlan.LemmaSeven`)

The seven pure functions `B₁,…,B₇` of Calegari–Dimitrov–Tang (arXiv:2408.15403, §"Pure functions",
eqs. `(defB)`, `(defB5)`, `(defB67)`) are `ℚ(y)`-linearly independent (paper Lemma `seven`).

The proof follows the *algebraic* route rather than the paper's monodromy argument: pull the
functions back along the rational parametrisation `y = x²/(x-1)`, where they become
`B₂∘y = 2y - x(x-2)log(1-x)/(x-1)`, `B₃∘y = -log²(1-x)/2`, `B₄∘y = (x - x/(x-1))(2Li₂(x) + log²(1-x)/2)`,
`B₅∘y = x·J(x)/(x-1)` with `2x(x-1)J' - xJ = 2(1-x)log(1-x)`, and `B₆, B₇` are the primitives of
`B₃/y`, `B₄/y`.  The `ℚ(x)`-independence of `1, log(1-x), log²(1-x), Li₂, J` is proved by
differentiating a putative relation and reducing to the classical facts that `log(1-x)` is not
rational and that `±1/(2(x-1))`, `2(x-2)²/(x-1)²` and `(x-2)/(x(x-1))` are not derivatives in `ℚ(x)`
(no simple poles); the two primitives are handled by differentiating the relation once more and
reading off the coefficients of `B₃/y`, `B₄/y`.  Finally the injectivity of `ℚ[y] → ℚ[x]`,
`P ↦ P(y(x))`, descends the independence of the pullbacks to `B₁,…,B₇` themselves.
-/

namespace Work.C7

open Submission.CDTPlan

/-- Paper Lemma `seven`: the seven pure functions are `ℚ(y)`-linearly independent. -/
theorem lemma_seven : LemmaSeven := pureB_independent

end Work.C7
