/-
# ZeroFreeTables/P9/prim/SigmaP3L_eq_logDeriv_derivs

The consumption step of the P9 stack: the sign/moment identity

  `((L'/L)^{(j)})(s).re = (-1)^{j+1} · M_j`,   `M_j = Σ_n Λ(n) Re(χ(n)n^{-s}) (log n)^j`,

is substituted into the moment expansion of `SigmaP3L` (HB (8.4), coefficient-correct weight
`u(y) = α + α²y + (1/3)α³y²`) to write HB's `Σ(s,χ)` directly in terms of the logarithmic
derivative and its first two iterated derivatives:

  `Σ(s,χ) = -(α/L)·(L'/L)(s).re + (α/L)²·(L'/L)'(s).re - (1/3)(α/L)³·(L'/L)''(s).re`.

This is the form in which the §9 zero-free estimate is applied, through the explicit formula
for `(L'/L)^{(j)}` (`lDiffExplicit_gen`) and the log-derivative hypothesis `LogDerivHyp`.

The `j = 1` instance, `M_1 = (iteratedDeriv 1 (L'/L)(s)).re`, is isolated as the base case
of the consumption: it is the first moment that contributes with a positive coefficient.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P9.prim.SigmaP3L_eq_moments
import Submission.Work.ZeroFreeTables.P9.prim.iteratedDeriv_logDeriv_re

namespace Work.ZeroFreeTables.P9.prim

open Work.ZeroFreeTables

/-- Base case `j = 1` of the moment/derivative conversion: the first logarithmic moment of the
twisted von Mangoldt series is the real part of the first derivative of `L'/L`. -/
lemma vonMangoldtMoment_one_eq_iteratedDeriv {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    vonMangoldtMoment χ s 1
      = (iteratedDeriv 1 (logDeriv (DirichletCharacter.LFunction χ)) s).re := by
  simpa using (iteratedDeriv_logDeriv_re χ 1 hs).symm

/-- HB's `Σ(s,χ)` in terms of `L'/L` and its first two iterated derivatives. -/
theorem SigmaP3L_eq_logDeriv_derivs {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) (a lam₁ L : ℝ) :
    SigmaP3L N L χ s a lam₁
      = -((a + lam₁) / L) * (logDeriv (DirichletCharacter.LFunction χ) s).re
        + ((a + lam₁) / L) ^ 2 *
            (iteratedDeriv 1 (logDeriv (DirichletCharacter.LFunction χ)) s).re
        - (1 / 3) * ((a + lam₁) / L) ^ 3 *
            (iteratedDeriv 2 (logDeriv (DirichletCharacter.LFunction χ)) s).re := by
  have h0 : (logDeriv (DirichletCharacter.LFunction χ) s).re
      = (-1 : ℝ) ^ (0 + 1) * vonMangoldtMoment χ s 0 := by
    simpa using iteratedDeriv_logDeriv_re χ 0 hs
  have h1 : (iteratedDeriv 1 (logDeriv (DirichletCharacter.LFunction χ)) s).re
      = vonMangoldtMoment χ s 1 := (vonMangoldtMoment_one_eq_iteratedDeriv χ hs).symm
  have h2 := iteratedDeriv_logDeriv_re χ 2 hs
  rw [SigmaP3L_eq_moments χ hs a lam₁ L, h0, h1, h2]
  ring

end Work.ZeroFreeTables.P9.prim
