import Mathlib
import Submission.Work.FIArea6Hecke.R.ConductorThetaDefs
import Submission.Work.FIArea5.S16Hecke.thetaOdd_aux
import Submission.Work.FIArea5.S16Hecke.ThetaDefs

namespace Work.FIArea6Hecke

open scoped BigOperators

/-- The Gauss sum `condGaussSum M chi₀ ξ` is bounded by `(gnorm M)²`: it is a double sum of
`gnorm M ^ 2` terms each of norm `≤ 1` (`‖χ₀‖ ≤ 1` and the exponential factor is a unit). -/
theorem norm_condGaussSum_le (M : GaussianInt) (chi₀ : GaussianInt → ℂ)
    (hchi : Work.FIArea6Hecke.R.IsCharModStrict M chi₀) (ξ : GaussianInt) :
    ‖Work.FIArea6Hecke.R.condGaussSum M chi₀ ξ‖ ≤ (((Work.FIPlan.gnorm M : ℕ) : ℝ)) ^ 2 := by
  rw [Work.FIArea6Hecke.R.condGaussSum]
  have hterm : ∀ a b : ℕ,
      ‖chi₀ (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt) *
        Complex.exp (2 * Real.pi * Complex.I *
          (((((a : ℤ) * ξ.re + (b : ℤ) * ξ.im : ℤ)) : ℂ) /
            ((Work.FIPlan.gnorm M : ℕ) : ℂ)))‖ ≤ (1 : ℝ) := by
    intro a b
    rw [show (2 * Real.pi * Complex.I *
            (((((a : ℤ) * ξ.re + (b : ℤ) * ξ.im : ℤ)) : ℂ) /
              ((Work.FIPlan.gnorm M : ℕ) : ℂ)))
          = ((↑((2 * Real.pi) *
                (((((a : ℤ) * ξ.re + (b : ℤ) * ξ.im : ℤ)) : ℝ) /
                  ((Work.FIPlan.gnorm M : ℕ) : ℝ))) : ℂ) * Complex.I) by
        push_cast; ring,
      norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    exact hchi.2.2.1 _
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hterm a b) ?_
  have h : (∑ _a ∈ Finset.range (Work.FIPlan.gnorm M),
      ∑ _b ∈ Finset.range (Work.FIPlan.gnorm M), (1 : ℝ))
      = (((Work.FIPlan.gnorm M : ℕ) : ℝ)) ^ 2 := by
    simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  exact le_of_eq h

theorem allZGaussKernelSummable (M : GaussianInt) (chi₀ : GaussianInt → ℂ)
    (hchi : Work.FIArea6Hecke.R.IsCharModStrict M chi₀) {u : ℝ} (hu : 0 < u)
    (hq : 0 < Work.FIPlan.gnorm M) (a b : ℕ) :
    Summable (fun ξ : ℤ × ℤ => Work.FIArea6Hecke.R.condGaussSum M chi₀ (⟨ξ.1, ξ.2⟩ : GaussianInt) *
      ((FourierTransform.fourier (fun x : ℝ => ((x : ℂ) ^ a) *
            Complex.exp (-Real.pi * u * (x : ℂ) ^ 2))) ((ξ.1 : ℝ) / ((Work.FIPlan.gnorm M : ℕ) : ℝ))
        * (FourierTransform.fourier (fun y : ℝ => ((y : ℂ) ^ b) *
            Complex.exp (-Real.pi * u * (y : ℂ) ^ 2))) ((ξ.2 : ℝ) / ((Work.FIPlan.gnorm M : ℕ) : ℝ)))) := by
  have hq' : (0 : ℝ) < ((Work.FIPlan.gnorm M : ℕ) : ℝ) := by exact_mod_cast hq
  have hA : Summable (fun n : ℤ =>
      (FourierTransform.fourier (fun x : ℝ => ((x : ℂ) ^ a) *
        Complex.exp (-Real.pi * u * (x : ℂ) ^ 2))) ((n : ℝ) / ((Work.FIPlan.gnorm M : ℕ) : ℝ))) :=
    Work.FIArea5.S16Hecke.fourier_kernel_summable u hu a hq'
  have hB : Summable (fun n : ℤ =>
      (FourierTransform.fourier (fun y : ℝ => ((y : ℂ) ^ b) *
        Complex.exp (-Real.pi * u * (y : ℂ) ^ 2))) ((n : ℝ) / ((Work.FIPlan.gnorm M : ℕ) : ℝ))) :=
    Work.FIArea5.S16Hecke.fourier_kernel_summable u hu b hq'
  refine Summable.of_norm_bounded (g := fun ξ : ℤ × ℤ =>
      ((((Work.FIPlan.gnorm M : ℕ) : ℝ)) ^ 2) *
      (‖(FourierTransform.fourier (fun x : ℝ => ((x : ℂ) ^ a) *
          Complex.exp (-Real.pi * u * (x : ℂ) ^ 2))) ((ξ.1 : ℝ) / ((Work.FIPlan.gnorm M : ℕ) : ℝ))‖ *
       ‖(FourierTransform.fourier (fun y : ℝ => ((y : ℂ) ^ b) *
          Complex.exp (-Real.pi * u * (y : ℂ) ^ 2))) ((ξ.2 : ℝ) / ((Work.FIPlan.gnorm M : ℕ) : ℝ))‖)) ?_ ?_
  · refine (Summable.mul_left _ ?_)
    exact Summable.mul_of_nonneg hA.norm hB.norm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  · intro ξ
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (norm_condGaussSum_le M chi₀ hchi ⟨ξ.1, ξ.2⟩)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))

end Work.FIArea6Hecke
