import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P9.iteratedDeriv_vonMangoldt
import Submission.Work.ZeroFreeTables.P9.SigmaP3LCoeffs
import Submission.Work.ZeroFreeTables.P9.iteratedDeriv_logDeriv_re
import Submission.Work.ZeroFreeTables.P9.SigmaP3L_eq_moments

namespace Work.ZeroFreeTables.P9

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
  have h1 := iteratedDeriv_logDeriv_re χ 1 hs
  have h2 := iteratedDeriv_logDeriv_re χ 2 hs
  rw [SigmaP3L_eq_moments χ hs a lam₁ L, h0, h1, h2]
  ring

end Work.ZeroFreeTables.P9
