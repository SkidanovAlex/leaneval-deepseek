import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_two_le
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi

namespace Work.LinnikAreas

/-- For a Dirichlet character `χ` modulo `N ≠ 0` and a point `s` with `1 ≤ Re s ≤ 2`, the real
part of the logarithmic derivative of the archimedean gamma factor
`gammaFactor χ = Γℝ(· + a)` (`a = 0` for even `χ`, `a = 1` for odd `χ`) is at most
`(log π)/2 + 4 + (1/2)·log(2 + |Im s| / 2)`.

Proof route: `gammaFactor χ s` equals `Complex.Gammaℝ s` (even `χ`) or `Complex.Gammaℝ (s+1)`
(odd `χ`); `Commons.Analysis.SpecialFunctions.Gamma.logDeriv_GammaR_off_pole` gives
`logDeriv Gammaℝ z = -(log π)/2 + digamma (z/2) / 2` off the poles (true here because
`Re z > 0`), then `Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound` bounds
`‖digamma (x + y * I)‖ ≤ log(2 + |y|) + 8` for `1/4 ≤ x ≤ 8`; here `x = Re(z/2) ∈ [1/4, 8]`
(from `1 ≤ Re s ≤ 2`) and `y = Im(z/2) = s.im / 2`; finally
`Re (logDeriv ...) ≤ ‖logDeriv ...‖` and `-(log π)/2 ≤ (log π)/2`. -/
theorem gammaFactor_logDeriv_re_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (h1 : 1 ≤ s.re) (h2 : s.re ≤ 2) :
    (logDeriv (DirichletCharacter.gammaFactor χ) s).re ≤
      Real.log Real.pi / 2 + 4 + (1 / 2) * Real.log (2 + |s.im| / 2) := by
  -- Reduction to `Γℝ` at a point `z` with `z.im = s.im` and `1/2 ≤ z.re ≤ 3`.
  have key : ∀ z : ℂ, (1 / 2 : ℝ) ≤ z.re → z.re ≤ 3 → z.im = s.im →
      (logDeriv Complex.Gammaℝ z).re ≤
        Real.log Real.pi / 2 + 4 + (1 / 2) * Real.log (2 + |s.im| / 2) := by
    intro z hz1 hz2 hzim
    have hz : 0 < z.re := by linarith
    -- the digamma estimate at `z / 2`
    have hw1 : (1 : ℝ) / 4 ≤ (z / 2).re := by
      rw [Commons.NumberTheory.DirichletCharacter.re_div_two]; linarith
    have hw2 : (z / 2).re ≤ 8 := by
      rw [Commons.NumberTheory.DirichletCharacter.re_div_two]; linarith
    have hdg := Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound
      (z / 2).re (z / 2).im hw1 hw2
    have harg : ((z / 2).re : ℂ) + ((z / 2).im : ℂ) * Complex.I = z / 2 := by
      conv_rhs => rw [← Complex.re_add_im (z / 2)]
    rw [harg] at hdg
    have hwim : |(z / 2).im| = |s.im| / 2 := by
      rw [Commons.NumberTheory.DirichletCharacter.im_div_two, hzim, abs_div]
      simp
    rw [hwim] at hdg
    -- the formula for `logDeriv Γℝ` and its real part
    have hformula := Commons.NumberTheory.DirichletCharacter.logDeriv_Gammaℝ_formula z hz
    rw [hformula]
    have hsplit : (-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma (z / 2) / 2).re
        = -(Real.log Real.pi) / 2 + (Complex.digamma (z / 2)).re / 2 := by
      rw [← Complex.ofReal_log (le_of_lt Real.pi_pos)]
      simp [Complex.add_re]
    rw [hsplit]
    have hre : (Complex.digamma (z / 2)).re ≤ ‖Complex.digamma (z / 2)‖ := Complex.re_le_norm _
    have hlogpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
    linarith
  rcases χ.even_or_odd with hE | hO
  · have hfun : DirichletCharacter.gammaFactor χ = Complex.Gammaℝ :=
      funext fun z => hE.gammaFactor_def z
    rw [hfun]
    exact key s (by linarith) (by linarith) rfl
  · have hfun : DirichletCharacter.gammaFactor χ = (fun z : ℂ => Complex.Gammaℝ (z + 1)) :=
      funext fun z => hO.gammaFactor_def z
    rw [hfun]
    have hld : logDeriv (fun z : ℂ => Complex.Gammaℝ (z + 1)) s =
        logDeriv Complex.Gammaℝ (s + 1) := by
      simp only [logDeriv, Pi.div_apply, deriv_comp_add_const]
    rw [hld]
    refine key (s + 1) ?_ ?_ ?_
    · rw [Complex.add_re]; simp; linarith
    · rw [Complex.add_re]; simp; linarith
    · rw [Complex.add_im]; simp

end Work.LinnikAreas
