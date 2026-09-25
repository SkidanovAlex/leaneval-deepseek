import Mathlib

open scoped ContDiff

namespace Work.Analysis.Fourier

/-- Derivative of the modulation `x ↦ exp(2πi a x)`: it is `(2πi a) •` itself. -/
private lemma hasDerivAt_modulation (a : ℝ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (↑(2 * Real.pi * a * y) * Complex.I))
      (((2 * Real.pi * a : ℝ) • Complex.I)
        * Complex.exp (↑(2 * Real.pi * a * x) * Complex.I)) x := by
  have hx : ∀ y : ℝ, (↑(2 * Real.pi * a * y) : ℂ) * Complex.I
      = y • ((2 * Real.pi * a : ℝ) • Complex.I) := by
    intro y
    rw [smul_smul, Complex.real_smul]
    push_cast
    ring
  have h := hasDerivAt_exp_smul_const' ((2 * Real.pi * a : ℝ) • Complex.I) x
  have h2 : (fun y : ℝ => Complex.exp ((↑(2 * Real.pi * a * y) : ℂ) * Complex.I))
      = fun u : ℝ => NormedSpace.exp (u • ((2 * Real.pi * a : ℝ) • Complex.I)) := by
    funext y; rw [hx y, Complex.exp_eq_exp_ℂ]
  have h3 : Complex.exp ((↑(2 * Real.pi * a * x) : ℂ) * Complex.I)
      = NormedSpace.exp (x • ((2 * Real.pi * a : ℝ) • Complex.I)) := by
    rw [hx x, Complex.exp_eq_exp_ℂ]
  rw [h2, h3]
  exact h

private lemma deriv_modulation (a : ℝ) :
    deriv (fun x : ℝ => Complex.exp (↑(2 * Real.pi * a * x) * Complex.I))
      = fun x => ((2 * Real.pi * a : ℝ) • Complex.I)
          * Complex.exp (↑(2 * Real.pi * a * x) * Complex.I) := by
  funext x
  exact (hasDerivAt_modulation a x).deriv

/-- All iterated derivatives of the modulation are `(2πi a)^n` times the modulation itself. -/
private lemma iteratedDeriv_modulation (a : ℝ) (n : ℕ) :
    iteratedDeriv n (fun x : ℝ => Complex.exp (↑(2 * Real.pi * a * x) * Complex.I))
      = fun x => ((2 * Real.pi * a : ℝ) • Complex.I) ^ n
          * Complex.exp (↑(2 * Real.pi * a * x) * Complex.I) := by
  induction n with
  | zero => funext x; simp [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ', deriv_modulation a]
    trans fun x => ((2 * Real.pi * a : ℝ) • Complex.I) *
        iteratedDeriv n (fun x : ℝ => Complex.exp (↑(2 * Real.pi * a * x) * Complex.I)) x
    · funext x; exact iteratedDeriv_const_mul_field _ _
    · rw [ih]; funext x; rw [pow_succ]; ring

theorem modulation_temperate_growth (a : ℝ) :
    Function.HasTemperateGrowth (fun x : ℝ => Complex.exp (↑(2 * Real.pi * a * x) * Complex.I)) := by
  have hcont : ContDiff ℝ ∞
      (fun x : ℝ => Complex.exp (↑(2 * Real.pi * a * x) * Complex.I)) := by
    have hu : ContDiff ℝ ∞ (fun y : ℝ => y • ((2 * Real.pi * a : ℝ) • Complex.I)) :=
      (ContinuousLinearMap.toSpanSingleton ℝ ((2 * Real.pi * a : ℝ) • Complex.I)).contDiff
    have h1 : (fun y : ℝ => y • ((2 * Real.pi * a : ℝ) • Complex.I))
        = fun y : ℝ => (↑(2 * Real.pi * a * y) : ℂ) * Complex.I := by
      funext y; rw [smul_smul, Complex.real_smul]; push_cast; ring
    rw [h1] at hu
    exact hu.cexp
  refine ⟨hcont, fun n => ⟨0, ‖((2 * Real.pi * a : ℝ) • Complex.I)‖ ^ n, fun x => ?_⟩⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_modulation a n]
  simp only [norm_mul, norm_pow, Complex.norm_exp_ofReal_mul_I, mul_one, pow_zero]
  exact le_refl _

end Work.Analysis.Fourier
