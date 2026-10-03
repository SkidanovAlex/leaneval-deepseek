import Mathlib
import Submission.Work.A3.Circle

/-!
# The divided difference of a polynomial (base definitions for `completeSum_power_saving`)

`polydiff g h` is the polynomial `(g(X+h) - g(X))/h ∈ ℤ[X]` (for `h ≠ 0`), written with
explicit integer coefficients, so that no division in `ℤ[X]` is needed:

`polydiff g h = ∑_{i} g.coeff i • ∑_{j<i} binom(i,j) h^{i-j-1} X^j`.

Its two uses in the proof of `Work.A3.completeSum_power_saving` are

* the *evaluation identity* `h * (polydiff g h).eval t = g.eval (t+h) - g.eval t`, which turns the
  differenced exponential sum `Σ_r e(-a (g(r+h) - g(r))/n)` into a complete sum of `polydiff g h`,
* its degree and leading coefficient: if `natDegree g = e` and `h ≠ 0` then `natDegree` of
  `polydiff g h` is `e - 1` and its leading coefficient is `e * g.leadingCoeff` — independent of
  `h`, which is what makes the induction on the degree close.
-/

set_option autoImplicit false

namespace Work.A3

open Polynomial Finset

noncomputable section

/-- The divided difference `(g(X+h) - g(X))/h`, with explicit integer coefficients. -/
def polydiff (g : ℤ[X]) (h : ℤ) : ℤ[X] :=
  ∑ i ∈ g.support, C (g.coeff i) *
    ∑ j ∈ Finset.range i, C ((i.choose j : ℤ) * h ^ (i - j - 1)) * X ^ j

end

end Work.A3
