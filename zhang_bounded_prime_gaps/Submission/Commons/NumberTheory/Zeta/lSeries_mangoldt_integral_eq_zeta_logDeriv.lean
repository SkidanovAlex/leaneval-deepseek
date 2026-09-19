import Mathlib.NumberTheory.LSeries.Dirichlet
import Submission.Commons.NumberTheory.Zeta.isPreconnected_re_gt_sdiff

namespace Commons.NumberTheory.Zeta

theorem lSeries_mangoldt_integral_eq_zeta_logDeriv (x : ℝ) (σ T : ℝ) (hσ1 : 1 < σ) :
    (∫ (t : ℝ) in -T..T,
        (LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
            ((σ : ℂ) + Complex.I * (t : ℂ))) *
          (x : ℂ) ^ ((σ : ℂ) + Complex.I * (t : ℂ)) /
          ((σ : ℂ) + Complex.I * (t : ℂ)))
      = ∫ (t : ℝ) in -T..T,
          (-(deriv riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))) /
            riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))) *
          (x : ℂ) ^ ((σ : ℂ) + Complex.I * (t : ℂ)) /
          ((σ : ℂ) + Complex.I * (t : ℂ)) := by
  apply congrArg (fun f : ℝ → ℂ => ∫ (t : ℝ) in -T..T, f t)
  funext t
  set s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
  have hs : 1 < s.re := by
    simpa [s] using hσ1
  have hL : LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s =
      -(deriv riemannZeta s) / riemannZeta s := by
    simpa using (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := s) hs)
  rw [hL]

end Commons.NumberTheory.Zeta