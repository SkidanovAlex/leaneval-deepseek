import Mathlib

/-!
# Definitions for the Jacobi triple product

The two functions whose equality is the Jacobi triple product (in the nome variable `x`
and the `z`-variable of the target statement):

* `jtpTheta x z = ∑' n : ℤ, x ^ (n^2) * z ^ n` (the two-sided theta series), and
* `jtpLHS x z = ∏' n : ℕ, (1 - x^(2(n+1))) * (1 + x^(2n+1) z) * (1 + x^(2n+1)/z)`.

Both satisfy the functional equation `F (x^2 * z) = (x*z)⁻¹ * F z` (for `x ≠ 0`), obtained
from the reindexing `n ↦ n + 1` in the exponent; together with holomorphy on `ℂ \ {0}`
this pins `F` down up to a scalar multiple of `jtpTheta x` (the rigidity lemma).
-/

namespace Work.Haupt

noncomputable section

open scoped BigOperators

/-- The two-sided theta series `∑_{n ∈ ℤ} x^{n²} z^n`. -/
def jtpTheta (x z : ℂ) : ℂ := ∑' n : ℤ, x ^ (n ^ 2) * z ^ n

/-- The Jacobi triple product as a function of `(x, z)`. -/
def jtpLHS (x z : ℂ) : ℂ :=
  ∏' n : ℕ, (1 - x ^ (2 * (n + 1))) * (1 + x ^ (2 * n + 1) * z) * (1 + x ^ (2 * n + 1) / z)

end

end Work.Haupt
