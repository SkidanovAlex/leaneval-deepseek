/-
  WilE9 / Sharp — the numerical constants of the degree bound for the extended system.

  The extended set `exSemiPf n m E L` is described by the stratum's own data plus the single
  cleared equation `exEq6`, whose degree is bounded in terms of

  * `E.deg` (the degree budget of the stratum),
  * `|L|` (the order of the derivative), and
  * an *a priori* bound on the format and on the fibre dimension.

  Every bound below is therefore a polynomial in `(E.deg, |L|, a₀)`; the constants collected
  here are the raw `ℕ`-values of the intermediate estimates, so that the final polynomial
  `b : MvPolynomial (Fin 3) ℕ` is *literally* `A3 n a₀ * (1+X₀)² (1+X₁)²`.
-/
import Mathlib

set_option autoImplicit false

namespace Work.WilE9.Sharp

/-- `2n + a₀ + 3`, an upper bound for the fibre dimension `qpb n m` whenever `m ≤ a₀`. -/
def qm (n a₀ : ℕ) : ℕ := 2 * n + a₀ + 3

/-- `4 (q³ + q² + q + 1)` at `q = qm n a₀`: the shape of the degree increment of
`iftP_totalDegree_le`, evaluated at the maximal admissible fibre dimension. -/
def bm (n a₀ : ℕ) : ℕ := 4 * (qm n a₀ ^ 3 + qm n a₀ ^ 2 + qm n a₀ + 1)

/-- `1 + bm`, absorbing the factor `1 + |L| * bm` of the estimate. -/
def Gc (n a₀ : ℕ) : ℕ := 1 + bm n a₀

/-- The coefficient of `(E.deg + 2) * (|L| + 1)` in the bound for `atomDeg (exEq6 …)`. -/
def A1 (n a₀ : ℕ) : ℕ := (qm n a₀ + 1) * Gc n a₀ * (n + 2)

/-- `A1` with the additive `n + 3` absorbed into the coefficient. -/
def A2 (n a₀ : ℕ) : ℕ := A1 n a₀ + n + 3

/-- The final constant: `deg (exSemiPf n m E L) ≤ A3 * (|L|+1) * (E.deg+1)²`. -/
def A3 (n a₀ : ℕ) : ℕ := 5 * n + 12 + 2 * A2 n a₀

end Work.WilE9.Sharp
