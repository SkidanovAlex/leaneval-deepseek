import Mathlib
import Submission.Work.CKFinal.LineDecay.Defs
import Submission.Work.CKFinal.LineDecay.model_base

/-!
# The `model_int_left` integral identity

This is the closed-form evaluation of the left horizontal-edge integral of the cusp model
`𝒢_G(τ,z) = G₀₀ + zG₀₁ + e^{-2πiz}(G₁₀ + zG₁₁)`:

`∫_{-1}^0 𝒢_G(τ, x+i+1) e^{iλ(x+i)} dx = e^{-λ}(G₀₀ QB λ + G₀₁ PB λ)
   + e^{-(λ-2π)}(G₁₀ QB(λ-2π) + G₁₁ PB(λ-2π))`,  `λ = π r²`.

The proof expands `Gmodel` in the second variable, uses the shift identities
`e^{iλ(x+i)} = e^{-λ}e^{iλx}` (`exp_split`) and
`e^{-2πi(x+i+1)}e^{iλ(x+i)} = e^{-(λ-2π)}e^{i(λ-2π)x}` (periodicity + `mul_exp`),
and then integrates the four continuous pieces term by term.
-/

open MeasureTheory UpperHalfPlane

namespace Work.CKFinal.LineDecay

/-- Pointwise expansion of the `model_int_left` integrand: the cusp model `Gmodel` splits into
its four coefficient pieces, each with the appropriate exponential weight. -/
lemma model_int_left_integrand (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (τ : UpperHalfPlane)
    (k x : ℝ) :
    Work.CKFinal.Gmodel G τ (((x : ℂ) + Complex.I) + 1)
        * Complex.exp (Complex.I * (k : ℂ) * ((x : ℂ) + Complex.I))
      = Complex.exp (-(k : ℂ)) * G 0 0 τ * Eexp k x
        + Complex.exp (-(k : ℂ)) * G 0 1 τ * (((x : ℂ) + Complex.I + 1) * Eexp k x)
        + Complex.exp (-(((k - 2 * Real.pi : ℝ)) : ℂ)) * G 1 0 τ * Eexp (k - 2 * Real.pi) x
        + Complex.exp (-(((k - 2 * Real.pi : ℝ)) : ℂ)) * G 1 1 τ
            * (((x : ℂ) + Complex.I + 1) * Eexp (k - 2 * Real.pi) x) := by
  have hC : Complex.exp (-(2 * Real.pi * Complex.I * (((x : ℂ) + Complex.I) + 1)))
      * (Complex.exp (-(k : ℂ)) * Eexp k x)
      = Complex.exp (-(((k - 2 * Real.pi : ℝ)) : ℂ)) * Eexp (k - 2 * Real.pi) x := by
    rw [← exp_split k x]
    rw [exp_per_add, mul_exp]
    rw [show Complex.I * ((k : ℂ) - ((2 * Real.pi : ℝ) : ℂ)) * ((x : ℂ) + Complex.I)
          = Complex.I * (((k - 2 * Real.pi : ℝ)) : ℂ) * ((x : ℂ) + Complex.I) by
        push_cast; ring]
    rw [exp_split]
  rw [Work.CKFinal.Gmodel]
  rw [exp_split k x]
  have hstep : (G 0 0 τ + ((x : ℂ) + Complex.I + 1) * G 0 1 τ
        + Complex.exp (-(2 * Real.pi * Complex.I * (((x : ℂ) + Complex.I) + 1)))
            * (G 1 0 τ + ((x : ℂ) + Complex.I + 1) * G 1 1 τ))
      * (Complex.exp (-(k : ℂ)) * Eexp k x)
      = (G 0 0 τ + ((x : ℂ) + Complex.I + 1) * G 0 1 τ) * (Complex.exp (-(k : ℂ)) * Eexp k x)
        + (G 1 0 τ + ((x : ℂ) + Complex.I + 1) * G 1 1 τ)
            * (Complex.exp (-(2 * Real.pi * Complex.I * (((x : ℂ) + Complex.I) + 1)))
                * (Complex.exp (-(k : ℂ)) * Eexp k x)) := by ring
  rw [hstep, hC]
  ring

/-- The four-term integral of `model_int_left_integrand`, evaluated term by term. -/
lemma model_int_left_linear (k : ℝ) (c1 c2 c3 c4 : ℂ) :
    (∫ x in (-1 : ℝ)..0, c1 * Eexp k x + c2 * (((x : ℂ) + Complex.I + 1) * Eexp k x)
        + c3 * Eexp (k - 2 * Real.pi) x
        + c4 * (((x : ℂ) + Complex.I + 1) * Eexp (k - 2 * Real.pi) x))
      = c1 * QB k + c2 * PB k + c3 * QB (k - 2 * Real.pi) + c4 * PB (k - 2 * Real.pi) := by
  have key : ∀ x : ℝ, c1 * Eexp k x + c2 * (((x : ℂ) + Complex.I + 1) * Eexp k x)
        + c3 * Eexp (k - 2 * Real.pi) x
        + c4 * (((x : ℂ) + Complex.I + 1) * Eexp (k - 2 * Real.pi) x)
      = c1 * Eexp k x + (c2 * (((x : ℂ) + Complex.I + 1) * Eexp k x)
        + (c3 * Eexp (k - 2 * Real.pi) x
            + c4 * (((x : ℂ) + Complex.I + 1) * Eexp (k - 2 * Real.pi) x))) := by
    intro x; ring
  simp_rw [key]
  rw [intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by simp only [Eexp]; fun_prop) (-1) 0)
        (Continuous.intervalIntegrable (by simp only [Eexp]; fun_prop) (-1) 0)]
  rw [intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by simp only [Eexp]; fun_prop) (-1) 0)
        (Continuous.intervalIntegrable (by simp only [Eexp]; fun_prop) (-1) 0)]
  rw [intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by simp only [Eexp]; fun_prop) (-1) 0)
        (Continuous.intervalIntegrable (by simp only [Eexp]; fun_prop) (-1) 0)]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  simp only [QB, PB]
  ring

theorem model_int_left (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) (r : ℝ) :
    (∫ x in (-1 : ℝ)..0,
        Work.CKFinal.Gmodel G τ (((x : ℂ) + (Work.CKFinal.hsplit : ℂ) * Complex.I) + 1)
          * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ)
              * ((x : ℂ) + (Work.CKFinal.hsplit : ℂ) * Complex.I)))
      = Complex.exp (-(((Real.pi * r ^ 2 : ℝ) : ℂ))) *
          (G 0 0 τ * QB (Real.pi * r ^ 2) + G 0 1 τ * PB (Real.pi * r ^ 2))
        + Complex.exp (-(((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ))) *
          (G 1 0 τ * QB (Real.pi * r ^ 2 - 2 * Real.pi)
            + G 1 1 τ * PB (Real.pi * r ^ 2 - 2 * Real.pi)) := by
  set k : ℝ := Real.pi * r ^ 2 with hk
  simp only [Work.CKFinal.hsplit, Complex.ofReal_one, one_mul]
  rw [intervalIntegral.integral_congr (fun x _ => model_int_left_integrand G τ k x)]
  rw [model_int_left_linear k (Complex.exp (-(k : ℂ)) * G 0 0 τ)
        (Complex.exp (-(k : ℂ)) * G 0 1 τ)
        (Complex.exp (-(((k - 2 * Real.pi : ℝ)) : ℂ)) * G 1 0 τ)
        (Complex.exp (-(((k - 2 * Real.pi : ℝ)) : ℂ)) * G 1 1 τ)]
  ring

end Work.CKFinal.LineDecay
