import Mathlib

/-!
# Definitions for the explicit bound on `-Re (ζ'/ζ)(σ)`

We record the two real Dirichlet series through which the logarithmic derivative of `ζ`
on the real axis is expressed:

* `zetaZ σ = ∑_{n ≥ 1} n^{-σ} = ζ(σ)`,
* `zetaW σ = ∑_{n ≥ 1} (log n) · n^{-σ} = -ζ'(σ)`.

The main point of the file `neg_zeta_logDeriv_re_le` is the elementary bound
`zetaW σ ≤ zetaZ σ / (σ - 1)` (`σ > 1`), which yields `-Re (ζ'/ζ)(σ) ≤ 1/(σ-1) + 1`.
-/

namespace Work.ZeroDensity.Jutila

/-- The Dirichlet series of the constant function `1` at the real point `σ`, i.e. `ζ(σ)`. -/
noncomputable def zetaZ (σ : ℝ) : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-σ)

/-- The Dirichlet series of `log` at the real point `σ`, i.e. `-ζ'(σ)`. -/
noncomputable def zetaW (σ : ℝ) : ℝ := ∑' n : ℕ, Real.log n * (n : ℝ) ^ (-σ)

end Work.ZeroDensity.Jutila
