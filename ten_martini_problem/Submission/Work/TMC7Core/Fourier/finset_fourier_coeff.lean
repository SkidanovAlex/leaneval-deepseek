import Mathlib
import Submission.Work.TMC7Core.Fourier.tail_L2_aux

/-!
# TMC7Core: Fourier coefficients of finite sums of exponential monomials

The `m`-th Fourier coefficient of a finite linear combination
`t ↦ ∑_{k ∈ S} a k * fourier k t` of exponential monomials on the circle `AddCircle 1`
is the corresponding coefficient `a m` when `m ∈ S`, and vanishes otherwise.
-/

namespace Work.TMC7Core.Fourier

/-- The Fourier coefficients of a finite linear combination of exponential monomials on
`AddCircle 1`: only the frequency `m` itself contributes, with coefficient `a m`.

This is the algebraic (finiteness) counterpart of the orthonormality of the monomials
`fourier n`, and is used to extract individual coefficients from finite trigonometric
polynomials. -/
theorem finset_fourier_coeff (S : Finset ℤ) (a : ℤ → ℂ) (m : ℤ) :
    fourierCoeff (fun t : AddCircle (1 : ℝ) => ∑ k ∈ S, a k * fourier k t) m
      = (if m ∈ S then a m else 0) := by
  classical
  -- Write the sum of functions as a function given by a pointwise sum.
  have hF : (∑ k ∈ S, (fun t : AddCircle (1 : ℝ) => a k * fourier k t))
      = fun t : AddCircle (1 : ℝ) => ∑ k ∈ S, a k * fourier k t := by
    funext t
    rw [Finset.sum_apply]
  rw [← hF,
    fourierCoeff.sum (T := 1) S (fun k => fun t : AddCircle (1 : ℝ) => a k * fourier k t)
      (fun k _ =>
        (continuous_const.mul (map_continuous (fourier k))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)),
    Finset.sum_apply]
  -- Each monomial contributes only its own frequency.
  have hterm : ∀ k : ℤ, fourierCoeff (fun t : AddCircle (1 : ℝ) => a k * fourier k t) m
      = (if m = k then a k else 0) := by
    intro k
    rw [fourierCoeff.const_mul, congr_fun (fourierCoeff_fourier (T := 1) k) m,
      Pi.single_apply, mul_ite, mul_one, mul_zero]
  simp only [hterm]
  exact Finset.sum_ite_eq S m a

end Work.TMC7Core.Fourier
