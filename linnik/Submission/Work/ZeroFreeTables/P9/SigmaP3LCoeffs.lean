/-
# ZeroFreeTables/P9/SigmaP3LCoeffs

The logarithmic moments of the twisted von Mangoldt `L`-series out of which the identity

`SigmaP3L χ s a λ₁ = -c·(logDeriv L_χ s).re + c²·(deriv (logDeriv L_χ) s).re
                        - (c³/3)·(deriv² (logDeriv L_χ) s).re`,  `c = (a+λ₁)/L`

is assembled: `c = (a+λ₁)/L` and, with `Ra n = Re(χ(n) n^{-s})`,

`SigmaP3L = L⁻¹ Σ_n Λ(n) Ra n (α + α²·(log n)/L + (α³/3)·((log n)/L)²)`
          `= c·M₀ + c²·M₁ + (c³/3)·M₂`,   `M_j = Σ_n Λ(n) Ra n (log n)^j`,

while for `Re s > 1`

`(logDeriv L_χ s).re = -M₀`, `(deriv (logDeriv L_χ) s).re = M₁`,
`(deriv² (logDeriv L_χ) s).re = -M₂`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL

open ArithmeticFunction

noncomputable section

namespace Work.ZeroFreeTables

/-- `Re (χ(n) n^{-s})`: the real part of the `n`-th summand of the twisted von Mangoldt
Dirichlet series `Σ_n Λ(n) χ(n) n^{-s}`. -/
def chiTwistRe {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) (n : ℕ) : ℝ :=
  ((χ (n : ZMod N) : ℂ) * (n : ℂ) ^ (-s)).re

/-- The `j`-th logarithmic moment `Σ_n Λ(n) Re(χ(n) n^{-s}) (log n)^j` of the twisted von
Mangoldt Dirichlet series.  Absolutely convergent for `Re s > 1`. -/
def vonMangoldtMoment {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) (j : ℕ) : ℝ :=
  ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * chiTwistRe χ s n * (Real.log n) ^ j

end Work.ZeroFreeTables
