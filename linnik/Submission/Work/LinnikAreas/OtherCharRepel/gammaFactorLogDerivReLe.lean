import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_two_le
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_mid_strip_le

/-!
# Real part of the logarithmic derivative of the archimedean gamma factor

For `γ = π^{-s/2} Γ(s/2)` (even character) or `π^{-(s+1)/2} Γ((s+1)/2)` (odd character) we
have, off the poles,
`logDeriv Γℝ z = -(log π)/2 + ψ(z/2)/2`, where `ψ = Γ'/Γ` is the digamma function
(`Commons.NumberTheory.DirichletCharacter.logDeriv_Gammaℝ_formula`).

The mid-strip digamma bound `‖ψ(x + iy)‖ ≤ log (2 + |y|) + 2` for `1/2 ≤ x ≤ 8`
(`Commons.Analysis.SpecialFunctions.Gamma.digamma_mid_strip_le`) then gives, for `Re z ≥ 1`
(so that `Re (z/2) ≥ 1/2`) and `z.im = τ`,

`Re (logDeriv Γℝ z) ≤ (1/2)·log (2 + |τ|) + 1`.

Since `gammaFactor χ` is either `Γℝ (·)` or `Γℝ (· + 1)`, and both `s` and `s + 1` have real
part `≥ 1` when `1 ≤ Re s ≤ 5/4`, this yields the required uniform upper bound with `C = 1`.
-/

namespace Work.LinnikAreas.OtherCharRepel

open Complex

/-- Pointwise form of the bound, for `Γℝ` itself: if `1 ≤ Re z ≤ 16` and `z.im = τ`, then
`Re (logDeriv Γℝ z) ≤ (1/2)·log (2 + |τ|) + 1`. -/
private theorem gammaR_logDeriv_re_le (z : ℂ) (τ : ℝ) (hz1 : 1 ≤ z.re) (hz2 : z.re ≤ 16)
    (hzim : z.im = τ) :
    (logDeriv Complex.Gammaℝ z).re ≤ (1 / 2) * Real.log (2 + |τ|) + 1 := by
  have hzpos : 0 < z.re := by linarith
  have hformula := Commons.NumberTheory.DirichletCharacter.logDeriv_Gammaℝ_formula z hzpos
  rw [hformula]
  have hsplit : (-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma (z / 2) / 2).re
      = -(Real.log Real.pi) / 2 + (Complex.digamma (z / 2)).re / 2 := by
    rw [← Complex.ofReal_log (le_of_lt Real.pi_pos)]
    simp [Complex.add_re]
  rw [hsplit]
  -- digamma bound at `z / 2`
  have hx1 : (1 : ℝ) / 2 ≤ (z / 2).re := by
    rw [Commons.NumberTheory.DirichletCharacter.re_div_two]; linarith
  have hx2 : (z / 2).re ≤ 8 := by
    rw [Commons.NumberTheory.DirichletCharacter.re_div_two]; linarith
  have hdg := Commons.Analysis.SpecialFunctions.Gamma.digamma_mid_strip_le
    (z / 2).re (z / 2).im hx1 hx2
  have harg : (((z / 2).re : ℂ) + ((z / 2).im : ℂ) * Complex.I) = z / 2 := by
    rw [Complex.re_add_im]
  rw [harg] at hdg
  have hwim : |(z / 2).im| = |τ| / 2 := by
    rw [Commons.NumberTheory.DirichletCharacter.im_div_two, hzim, abs_div]
    norm_num
  rw [hwim] at hdg
  have hlogle : Real.log (2 + |τ| / 2) ≤ Real.log (2 + |τ|) := by
    apply Real.log_le_log (by positivity)
    linarith [abs_nonneg τ]
  have hre : (Complex.digamma (z / 2)).re ≤ Real.log (2 + |τ|) + 2 :=
    le_trans (Complex.re_le_norm _) (by linarith)
  have hlogpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  linarith

theorem gammaFactorLogDerivReLe : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N) (σ τ : ℝ), 1 ≤ σ → σ ≤ 5 / 4 →
    (logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + Complex.I * (τ : ℂ))).re ≤
      (1 / 2) * Real.log (2 + |τ|) + C := by
  refine ⟨1, one_pos, ?_⟩
  intro N _inst χ σ τ hσ1 hσ2
  rcases χ.even_or_odd with hE | hO
  · -- even character: `gammaFactor χ = Gammaℝ`
    have hfun : DirichletCharacter.gammaFactor χ = Complex.Gammaℝ :=
      funext fun z => hE.gammaFactor_def z
    rw [hfun]
    exact gammaR_logDeriv_re_le _ τ (by simp; linarith) (by simp; linarith) (by simp)
  · -- odd character: `gammaFactor χ = Gammaℝ (· + 1)`
    have hfun : DirichletCharacter.gammaFactor χ = (fun z : ℂ => Complex.Gammaℝ (z + 1)) :=
      funext fun z => hO.gammaFactor_def z
    rw [hfun]
    have hld : logDeriv (fun z : ℂ => Complex.Gammaℝ (z + 1))
          ((σ : ℂ) + Complex.I * (τ : ℂ))
        = logDeriv Complex.Gammaℝ (((σ : ℂ) + Complex.I * (τ : ℂ)) + 1) := by
      simp only [logDeriv, Pi.div_apply, deriv_comp_add_const]
    rw [hld]
    exact gammaR_logDeriv_re_le _ τ (by simp [Complex.add_re]; linarith)
      (by simp [Complex.add_re]; linarith) (by simp)

end Work.LinnikAreas.OtherCharRepel
