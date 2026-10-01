import Mathlib
import Submission.Work.LinnikAreas.FarRepel.digammaDerivSeries
import Submission.Work.LinnikAreas.TuranOther.gammaRDerivSeries

namespace Work.LinnikAreas.TuranOther

-- Route: on `1 < Re s` one has `logDeriv Gammaℝ =ᶠ fun z => -(log π)/2 + (1/2) * digamma (z/2)`
-- (`Submission.Commons.Analysis.SpecialFunctions.Gamma.logDeriv_GammaR_off_pole`, importable at the
-- module path `Submission.Commons.Analysis.SpecialFunctions.Gamma.logDeriv_GammaR_off_pole`),
-- then `Work.LinnikAreas.FarRepel.digammaDerivSeries m hm (w := s/2) (by linarith)` with
-- `iteratedDeriv_const_add`, `iteratedDeriv_const_mul_field` and the chain rule
-- `iteratedDeriv (fun z => f (c*z)) = c^k * ...` (or the `FarRepel.digammaDerivSeries` module's
-- own chain-rule helpers); finally `(1/(s/2 + n))^(k+1) = 2^(k+1) * (1/(s+2n))^(k+1)` and
-- `(1/2)^(k+1) * 2^(k+1) = 1`.
--
-- This is exactly `Work.LinnikAreas.TuranOther.gammaRDerivSeries` (proved by the same route,
-- with the weaker hypothesis `0 < Re t`, from `logDeriv_GammaR_off_pole` +
-- `DhExplicit.iteratedDerivDigammaHalf` + `FarRepel.digammaDerivSeries`); the only difference is
-- the shape of the summand, `(2 * n : ℕ)` cast to `ℂ` versus `2 * (n : ℂ)`, which agree by
-- `Nat.cast_mul`.
theorem iteratedDeriv_logDeriv_GammaR (k : ℕ) (hk : 1 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv k (logDeriv Complex.Gammaℝ) s
      = (-1 : ℂ) ^ (k + 1) * (k.factorial : ℂ)
        * (∑' n : ℕ, (1 / (s + ((2 * n : ℕ) : ℂ))) ^ (k + 1)) := by
  have hs0 : 0 < s.re := by linarith
  rw [show (∑' n : ℕ, (1 / (s + ((2 * n : ℕ) : ℂ))) ^ (k + 1))
      = (∑' n : ℕ, (1 / (s + (2 * (n : ℂ)))) ^ (k + 1)) from
    tsum_congr fun n => by rw [Nat.cast_mul]; norm_num]
  exact gammaRDerivSeries k hk hs0

end Work.LinnikAreas.TuranOther
