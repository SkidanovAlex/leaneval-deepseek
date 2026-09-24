import Mathlib
import Submission.Work.GM.S3.Base

namespace Work.GM.S3

open MeasureTheory
open scoped FourierTransform

/-- The norm of `2 * π * I * x` as a complex number is `2 * π * |x|`. -/
private lemma norm_two_pi_I_mul_explicit (x : ℝ) :
    ‖(2 * Real.pi * Complex.I * (x : ℂ))‖ = 2 * Real.pi * |x| := by
  rw [norm_mul, norm_mul, norm_mul]
  simp only [Complex.norm_ofNat, Complex.norm_I, mul_one]
  rw [show ‖(Real.pi : ℂ)‖ = Real.pi by simp [abs_of_nonneg Real.pi_pos.le]]
  simp

/-- **Explicit-constant Fourier decay.** If `h : ℝ → ℂ` is `C^∞` with compact support and `ξ ≠ 0`,
then `‖𝓕 h ξ‖ ≤ (∫ ‖h^(j)‖) / (2π|ξ|)^j` (the constant of
`Commons.Analysis.Fourier.fourierTransform_iteratedDeriv_decay` made explicit).
Suggested route: `Real.fourier_iteratedDeriv` (with `N := (j : ℕ∞)`) gives
`𝓕 (h^(j)) x = (2πi x)^j • 𝓕 h x`; take norms, use `‖(2πiξ)^j‖ = (2π|ξ|)^j` and
`‖𝓕(h^(j))ξ‖ ≤ ∫ ‖h^(j)‖`. -/
theorem fourier_decay_explicit (j : ℕ) {h : ℝ → ℂ}
    (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h) (hcs : HasCompactSupport h)
    {ξ : ℝ} (hξ : ξ ≠ 0) :
    ‖FourierTransform.fourier h ξ‖ ≤ (∫ x, ‖iteratedDeriv j h x‖) / (2 * Real.pi * |ξ|) ^ j := by
  -- Every iterated derivative is continuous with compact support, hence integrable.
  have hint : ∀ n : ℕ, Integrable (iteratedDeriv n h) := by
    intro n
    have hsupp : HasCompactSupport (iteratedDeriv n h) := by
      rw [iteratedDeriv_eq_equiv_comp]
      exact (hcs.iteratedFDeriv (𝕜 := ℝ) n).comp_left (map_zero _)
    exact (hh.continuous_iteratedDeriv n (WithTop.coe_le_coe.mpr le_top)).integrable_of_hasCompactSupport
      hsupp
  -- `h` is `j` times continuously differentiable.
  have hhj : ContDiff ℝ (j : ℕ∞) h := hh.of_le (WithTop.coe_le_coe.mpr le_top)
  -- Differentiation becomes multiplication by `(2πi·)^j` under the Fourier transform.
  have hfour := Real.fourier_iteratedDeriv (f := h) (N := (j : ℕ∞)) (n := j) hhj
      (fun n _ => hint n) (by simp)
  have hfour' : ∀ x : ℝ, 𝓕 (iteratedDeriv j h) x
        = (2 * Real.pi * Complex.I * (x : ℂ)) ^ j • (𝓕 h x) := fun x => congrFun hfour x
  -- `A := ∫ ‖h^(j)‖` bounds the Fourier transform of the `j`-th derivative uniformly.
  set A : ℝ := ∫ y, ‖iteratedDeriv j h y‖ with hAdef
  have hAbound (η : ℝ) : ‖𝓕 (iteratedDeriv j h) η‖ ≤ A := by
    rw [Real.fourier_eq]
    refine (norm_integral_le_integral_norm _).trans ?_
    simp only [Circle.norm_smul]
    exact le_of_eq hAdef.symm
  have h2pi : ∀ η : ℝ, ‖(2 * Real.pi * Complex.I * (η : ℂ)) ^ j‖ = (2 * Real.pi * |η|) ^ j := by
    intro η
    rw [norm_pow, norm_two_pi_I_mul_explicit]
  have hξpos : 0 < |ξ| := abs_pos.mpr hξ
  have hDpos : 0 < (2 * Real.pi * |ξ|) ^ j := pow_pos (by positivity) j
  refine (le_div_iff₀ hDpos).mpr ?_
  calc ‖𝓕 h ξ‖ * (2 * Real.pi * |ξ|) ^ j
      = (2 * Real.pi * |ξ|) ^ j * ‖𝓕 h ξ‖ := by ring
    _ ≤ A := by
        have h := hAbound ξ
        rwa [hfour' ξ, norm_smul, h2pi ξ] at h
    _ = ∫ y, ‖iteratedDeriv j h y‖ := hAdef

end Work.GM.S3
