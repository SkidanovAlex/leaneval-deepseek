import Mathlib
import Submission.Work.CKFinal.LineDecay.Defs
import Submission.Work.CKFinal.LineDecay.shift_helpers

namespace Work.CKFinal.LineDecay

/-! # The horizontal pieces `P₂` as the shifted-line integrals `f₁` and `f₂`

`P₂` (see `Defs`) is written as `-i ∫_0^1 K(τ, x-1+ i) e^{iπr²(x+i)} dx
+ i ∫_{-1}^0 K(τ, x+1+i) e^{iπr²(x+i)} dx`, with the kernel evaluated through
`Kax K τ (x ∓ 1) H` at the split height `H = 1`.  The two `f`-functions
(`shift_helpers`) are the same integrands after passing to the complex variable
`z = x + i`, i.e. `f1fun z = K(τ, z-1) e^{iπr²z}` and `f2fun z = K(τ, z+1) e^{iπr²z}`.
The identity is therefore a pointwise rewriting of the integrands. -/

/-- Pointwise form of the first (`x - 1`) horizontal piece: the `Kax`-integrand at the height
`1` and the complex variable `z = x + i` is `f1fun` at `z`. -/
private lemma Kax_left_eq_f1fun (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (τ : UpperHalfPlane) (r x : ℝ) :
    Work.CKFinal.Kax (Work.Kernels.Kfun ℓ d) τ (x - 1) 1
      * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ) * ((x : ℂ) + (1 : ℂ) * Complex.I))
    = f1fun ℓ d τ r ((x : ℂ) + (1 : ℂ) * Complex.I) := by
  rw [Kax_eq_K_ofComplex]
  · rw [f1fun, kerExp_eq_phase]
    congr 2
    · congr 1
      push_cast; ring
    · ring
  · norm_num

/-- Pointwise form of the second (`x + 1`) horizontal piece: the `Kax`-integrand at the height
`1` and the complex variable `z = x + i` is `f2fun` at `z`. -/
private lemma Kax_right_eq_f2fun (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (τ : UpperHalfPlane) (r x : ℝ) :
    Work.CKFinal.Kax (Work.Kernels.Kfun ℓ d) τ (x + 1) 1
      * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ) * ((x : ℂ) + (1 : ℂ) * Complex.I))
    = f2fun ℓ d τ r ((x : ℂ) + (1 : ℂ) * Complex.I) := by
  rw [Kax_eq_K_ofComplex]
  · rw [f2fun, kerExp_eq_phase]
    congr 2
    · congr 1
      push_cast; ring
    · ring
  · norm_num

theorem P2_eq_neg_I_f1_add_I_f2 (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (τ : UpperHalfPlane) (r : ℝ) :
    Work.CKFinal.P2 (Work.Kernels.Kfun ℓ d) r τ
      = - Complex.I * (∫ x in (0 : ℝ)..1, Work.CKFinal.LineDecay.f1fun ℓ d τ r ((x : ℂ) + (1 : ℂ) * Complex.I))
        + Complex.I * (∫ x in (-1 : ℝ)..0, Work.CKFinal.LineDecay.f2fun ℓ d τ r ((x : ℂ) + (1 : ℂ) * Complex.I)) := by
  rw [Work.CKFinal.P2, Work.CKFinal.hsplit]
  simp only [Complex.ofReal_one]
  have hA : (∫ x in (0 : ℝ)..1, Work.CKFinal.Kax (Work.Kernels.Kfun ℓ d) τ (x - 1) 1
      * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ) * ((x : ℂ) + (1 : ℂ) * Complex.I)))
      = ∫ x in (0 : ℝ)..1, f1fun ℓ d τ r ((x : ℂ) + (1 : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact Kax_left_eq_f1fun ℓ d τ r x
  have hB : (∫ x in (-1 : ℝ)..0, Work.CKFinal.Kax (Work.Kernels.Kfun ℓ d) τ (x + 1) 1
      * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ) * ((x : ℂ) + (1 : ℂ) * Complex.I)))
      = ∫ x in (-1 : ℝ)..0, f2fun ℓ d τ r ((x : ℂ) + (1 : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact Kax_right_eq_f2fun ℓ d τ r x
  rw [hA, hB]

end Work.CKFinal.LineDecay
