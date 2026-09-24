import Mathlib.Analysis.Fourier.FourierTransformDeriv

namespace Commons.Analysis.Fourier

open MeasureTheory
open scoped FourierTransform

/-- The norm of `2 * π * I * x` as a complex number is `2 * π * |x|`. -/
private lemma norm_two_pi_I_mul (x : ℝ) :
    ‖(2 * Real.pi * Complex.I * (x : ℂ))‖ = 2 * Real.pi * |x| := by
  rw [norm_mul, norm_mul, norm_mul]
  simp only [Complex.norm_ofNat, Complex.norm_I, mul_one]
  rw [show ‖(Real.pi : ℂ)‖ = Real.pi by simp [abs_of_nonneg Real.pi_pos.le]]
  simp

theorem fourierTransform_iteratedDeriv_decay (j : ℕ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hcs : HasCompactSupport f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ, ξ ≠ 0 →
      ‖FourierTransform.fourier f ξ‖ ≤ C / |ξ| ^ j := by
  -- Every iterated derivative is continuous with compact support, hence integrable.
  have hint : ∀ n : ℕ, Integrable (iteratedDeriv n f) := by
    intro n
    have hsupp : HasCompactSupport (iteratedDeriv n f) := by
      rw [iteratedDeriv_eq_equiv_comp]
      exact (hcs.iteratedFDeriv (𝕜 := ℝ) n).comp_left (map_zero _)
    exact (hf.continuous_iteratedDeriv n (WithTop.coe_le_coe.mpr le_top)).integrable_of_hasCompactSupport
      hsupp
  -- `f` is `j` times continuously differentiable.
  have hfj : ContDiff ℝ (j : ℕ∞) f := hf.of_le (WithTop.coe_le_coe.mpr le_top)
  -- Differentiation becomes multiplication by `(2πi·)^j` under the Fourier transform.
  have hfour := Real.fourier_iteratedDeriv (f := f) (N := (j : ℕ∞)) (n := j) hfj
      (fun n _ => hint n) (by simp)
  have hfour' : ∀ x : ℝ, 𝓕 (iteratedDeriv j f) x
        = (2 * Real.pi * Complex.I * (x : ℂ)) ^ j • (𝓕 f x) := fun x => congrFun hfour x
  -- `A` bounds the Fourier transform of the `j`-th derivative uniformly.
  set A : ℝ := ∫ y, ‖iteratedDeriv j f y‖ with hAdef
  have hAbound (ξ : ℝ) : ‖𝓕 (iteratedDeriv j f) ξ‖ ≤ A := by
    rw [Real.fourier_eq]
    refine (norm_integral_le_integral_norm _).trans ?_
    simp only [Circle.norm_smul]
    exact le_of_eq hAdef.symm
  have hAnonneg : 0 ≤ A := by
    rw [hAdef]
    exact integral_nonneg (fun y => norm_nonneg _)
  have h2pi : ∀ ξ : ℝ, ‖(2 * Real.pi * Complex.I * (ξ : ℂ)) ^ j‖ = (2 * Real.pi * |ξ|) ^ j := by
    intro ξ
    rw [norm_pow, norm_two_pi_I_mul]
  have hkey (ξ : ℝ) : ‖𝓕 f ξ‖ * (2 * Real.pi * |ξ|) ^ j ≤ A := by
    have hb : (2 * Real.pi * |ξ|) ^ j * ‖𝓕 f ξ‖ ≤ A := by
      have h := hAbound ξ
      rwa [hfour' ξ, norm_smul, h2pi ξ] at h
    calc ‖𝓕 f ξ‖ * (2 * Real.pi * |ξ|) ^ j
        = (2 * Real.pi * |ξ|) ^ j * ‖𝓕 f ξ‖ := by ring
      _ ≤ A := hb
  refine ⟨A / (2 * Real.pi) ^ j, div_nonneg hAnonneg (by positivity), ?_⟩
  intro ξ hξ
  have hξpos : 0 < |ξ| := abs_pos.mpr hξ
  have hDpos : 0 < (2 * Real.pi * |ξ|) ^ j := pow_pos (by positivity) j
  have h1 : ‖𝓕 f ξ‖ ≤ A / (2 * Real.pi * |ξ|) ^ j := (le_div_iff₀ hDpos).mpr (hkey ξ)
  rw [mul_pow] at h1
  have h2 : A / ((2 * Real.pi) ^ j * |ξ| ^ j) = (A / (2 * Real.pi) ^ j) / |ξ| ^ j := by
    rw [div_div]
  rwa [h2] at h1

end Commons.Analysis.Fourier