/-
# ZeroFreeTables/lam0w/PrincipalDefs — the corrector objects of the principal `P₃` bound

The pole-extraction reduction of HB §9 for the principal character reduces the bound
`Σ(s,χ₀) ≤ Re P₃(α/((s-1)L)) + α e` to a bound for the `P₃`-operator applied to the
*corrector* of the log-derivative.  We fix here the three objects that the argument uses.

* `zetaCorr z = -ζ'/ζ(z) - 1/(z-1)`: the log-derivative of `ζ` with its pole at `1`
  subtracted (holomorphic across `1`, since `(z-1)ζ(z)` is entire and non-vanishing there).
* `princCorr q z = -L'/L(·,χ₀)(z) - 1/(z-1)`: the same for the principal character mod `q`.
* `eulFac q z = ∑_{p | q} log p/(p^z - 1)`: the Euler-factor correction, which is the
  *difference* of the two correctors (`princCorr q = zetaCorr - eulFac` on `Re z > 1`).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P9.SigmaP3L_eq_logDeriv_derivs

open DirichletCharacter Complex
open scoped BigOperators
noncomputable section

namespace Work.ZeroFreeTables.lam0w

/-- The log-derivative of `ζ` with its pole at `1` subtracted: `-ζ'/ζ(z) - 1/(z-1)`. -/
def zetaCorr (z : ℂ) : ℂ := -logDeriv riemannZeta z - (z - 1)⁻¹

/-- The log-derivative of the principal character's `L`-function mod `q`, with its pole at `1`
subtracted. -/
def princCorr (q : ℕ) [NeZero q] (z : ℂ) : ℂ :=
  -logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) z - (z - 1)⁻¹

/-- The Euler-factor sum `∑_{p | q} log p / (p^z - 1)` attached to the principal character
mod `q`.  On `Re z > 1` it is the difference `zetaCorr z - princCorr q z`. -/
def eulFac (q : ℕ) (z : ℂ) : ℂ :=
  ∑ p ∈ q.primeFactors, (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)

end Work.ZeroFreeTables.lam0w
