import Mathlib
import Submission.Work.CKFinal.LineDecay.Defs
import Submission.Work.CKFinal.LineDecay.model_base

/-!
# The right-hand horizontal-edge integral of the cusp model

We compute the integral, over the segment `[0,1]` of the line `Im w = H = 1`, of the cusp model
`𝒢_G(τ, w-1)` times `e^{iλw}` (`λ = π r²`), landing on the closed form
`e^{-πr²}(G₀₀QA(πr²) + G₀₁PA(πr²)) + e^{-(πr²-2π)}(G₁₀QA(πr²-2π) + G₁₁PA(πr²-2π))`.

The computation is a pointwise expansion of `Gmodel` (using `e^{-2πi(w-1)} = e^{-2πiw}` and
`e^{iλw} = e^{-λ}e^{iλx}` for `w = x + i`), followed by the interval integral of an affine
function against `e^{ikx}` (which is the definition of `QA`, `PA`).
-/

noncomputable section

open MeasureTheory UpperHalfPlane intervalIntegral

namespace Work.CKFinal.LineDecay

/-- Pointwise expansion of the right-hand integrand: expanding `Gmodel` and using
`e^{-2πi(w-1)} = e^{-2πiw}` together with `e^{iλ(x+i)} = e^{-λ}e^{iλx}` splits the integrand into
its `G₀•` part (frequency `λ = πr²`) and its `G₁•` part (frequency `λ - 2π`). -/
lemma Gmodel_pt_right (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) (r x : ℝ) :
    Work.CKFinal.Gmodel G τ (((x : ℂ) + Complex.I) - 1)
        * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ) * ((x : ℂ) + Complex.I))
      = Complex.exp (-(((Real.pi * r ^ 2 : ℝ) : ℂ)))
          * ((G 0 0 τ + (((x : ℂ) + Complex.I) - 1) * G 0 1 τ) * Eexp (Real.pi * r ^ 2) x)
        + Complex.exp (-(((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ)))
          * ((G 1 0 τ + (((x : ℂ) + Complex.I) - 1) * G 1 1 τ)
              * Eexp (Real.pi * r ^ 2 - 2 * Real.pi) x) := by
  rw [Work.CKFinal.Gmodel]
  rw [exp_per_sub ((x : ℂ) + Complex.I)]
  have hE : Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ) * ((x : ℂ) + Complex.I))
      = Complex.exp (-(((Real.pi * r ^ 2 : ℝ) : ℂ))) * Eexp (Real.pi * r ^ 2) x :=
    exp_split (Real.pi * r ^ 2) x
  have hce : Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℂ) + Complex.I)))
      * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ) * ((x : ℂ) + Complex.I))
      = Complex.exp (-(((Real.pi * r ^ 2 - 2 * Real.pi : ℝ)) : ℂ))
          * Eexp (Real.pi * r ^ 2 - 2 * Real.pi) x := by
    rw [mul_exp (Real.pi * r ^ 2) ((x : ℂ) + Complex.I)]
    rw [show Complex.I * (((Real.pi * r ^ 2 : ℝ) : ℂ) - ((2 * Real.pi : ℝ) : ℂ))
            * ((x : ℂ) + Complex.I)
          = Complex.I * (((Real.pi * r ^ 2 - 2 * Real.pi : ℝ)) : ℂ) * ((x : ℂ) + Complex.I) by
        push_cast; ring]
    rw [exp_split (Real.pi * r ^ 2 - 2 * Real.pi) x]
  have hdist :
      (G 0 0 τ + (((x : ℂ) + Complex.I) - 1) * G 0 1 τ
          + Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℂ) + Complex.I)))
              * (G 1 0 τ + (((x : ℂ) + Complex.I) - 1) * G 1 1 τ))
        * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ) * ((x : ℂ) + Complex.I))
      = (G 0 0 τ + (((x : ℂ) + Complex.I) - 1) * G 0 1 τ)
          * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ) * ((x : ℂ) + Complex.I))
        + (G 1 0 τ + (((x : ℂ) + Complex.I) - 1) * G 1 1 τ)
            * (Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℂ) + Complex.I)))
                * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ) * ((x : ℂ) + Complex.I))) := by
    ring
  rw [hdist, hce, hE]
  ring

/-- The interval integral of an affine function against `e^{ikx}`: this is the definition of
`QA`, `PA`. -/
lemma intervalIntegral_affine (k : ℝ) (a b : ℂ) :
    (∫ x in (0 : ℝ)..1, (a + (((x : ℂ) + Complex.I) - 1) * b) * Eexp k x)
      = a * QA k + b * PA k := by
  have hg : ∀ x : ℝ, (a + (((x : ℂ) + Complex.I) - 1) * b) * Eexp k x
      = a * Eexp k x + b * ((((x : ℂ) + Complex.I) - 1) * Eexp k x) := by
    intro x; ring
  have hI0 : IntervalIntegrable (fun x : ℝ => a * Eexp k x) volume (0:ℝ) 1 := by
    apply Continuous.intervalIntegrable
    show Continuous fun x : ℝ => a * Complex.exp (Complex.I * (k : ℂ) * (x : ℂ))
    fun_prop
  have hI1 : IntervalIntegrable
      (fun x : ℝ => b * ((((x : ℂ) + Complex.I) - 1) * Eexp k x)) volume (0:ℝ) 1 := by
    apply Continuous.intervalIntegrable
    show Continuous fun x : ℝ =>
      b * ((((x : ℂ) + Complex.I) - 1) * Complex.exp (Complex.I * (k : ℂ) * (x : ℂ)))
    fun_prop
  trans ∫ x in (0 : ℝ)..1,
      (a * Eexp k x + b * ((((x : ℂ) + Complex.I) - 1) * Eexp k x))
  · exact intervalIntegral.integral_congr (fun x _ => hg x)
  · rw [intervalIntegral.integral_add hI0 hI1]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    simp only [QA, PA]

theorem model_int_right (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) (r : ℝ) :
    (∫ x in (0 : ℝ)..1,
        Work.CKFinal.Gmodel G τ (((x : ℂ) + (Work.CKFinal.hsplit : ℂ) * Complex.I) - 1)
          * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ)
              * ((x : ℂ) + (Work.CKFinal.hsplit : ℂ) * Complex.I)))
      = Complex.exp (-(((Real.pi * r ^ 2 : ℝ) : ℂ))) *
          (G 0 0 τ * QA (Real.pi * r ^ 2) + G 0 1 τ * PA (Real.pi * r ^ 2))
        + Complex.exp (-(((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ))) *
          (G 1 0 τ * QA (Real.pi * r ^ 2 - 2 * Real.pi)
            + G 1 1 τ * PA (Real.pi * r ^ 2 - 2 * Real.pi)) := by
  simp only [hsplit_coe, one_mul]
  have hI1 : IntervalIntegrable
      (fun x : ℝ => Complex.exp (-(((Real.pi * r ^ 2 : ℝ) : ℂ)))
        * ((G 0 0 τ + (((x : ℂ) + Complex.I) - 1) * G 0 1 τ) * Eexp (Real.pi * r ^ 2) x))
      volume (0:ℝ) 1 := by
    apply Continuous.intervalIntegrable
    show Continuous fun x : ℝ => Complex.exp (-(((Real.pi * r ^ 2 : ℝ) : ℂ)))
      * ((G 0 0 τ + (((x : ℂ) + Complex.I) - 1) * G 0 1 τ)
          * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ) * (x : ℂ)))
    fun_prop
  have hI2 : IntervalIntegrable
      (fun x : ℝ => Complex.exp (-(((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ)))
        * ((G 1 0 τ + (((x : ℂ) + Complex.I) - 1) * G 1 1 τ)
            * Eexp (Real.pi * r ^ 2 - 2 * Real.pi) x))
      volume (0:ℝ) 1 := by
    apply Continuous.intervalIntegrable
    show Continuous fun x : ℝ => Complex.exp (-(((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ)))
      * ((G 1 0 τ + (((x : ℂ) + Complex.I) - 1) * G 1 1 τ)
          * Complex.exp (Complex.I * ((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ) * (x : ℂ)))
    fun_prop
  trans ∫ x in (0 : ℝ)..1,
      (Complex.exp (-(((Real.pi * r ^ 2 : ℝ) : ℂ)))
        * ((G 0 0 τ + (((x : ℂ) + Complex.I) - 1) * G 0 1 τ) * Eexp (Real.pi * r ^ 2) x)
      + Complex.exp (-(((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ)))
        * ((G 1 0 τ + (((x : ℂ) + Complex.I) - 1) * G 1 1 τ)
            * Eexp (Real.pi * r ^ 2 - 2 * Real.pi) x))
  · exact intervalIntegral.integral_congr (fun x _ => Gmodel_pt_right G τ r x)
  · rw [intervalIntegral.integral_add hI1 hI2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral_affine (Real.pi * r ^ 2) (G 0 0 τ) (G 0 1 τ),
      intervalIntegral_affine (Real.pi * r ^ 2 - 2 * Real.pi) (G 1 0 τ) (G 1 1 τ)]

end Work.CKFinal.LineDecay
