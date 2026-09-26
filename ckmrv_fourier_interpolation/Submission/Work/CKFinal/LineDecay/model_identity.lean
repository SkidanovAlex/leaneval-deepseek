import Mathlib
import Submission.Work.CKFinal.LineDecay.Defs
import Submission.Work.CKFinal.LineDecay.model_int_left
import Submission.Work.CKFinal.LineDecay.model_int_right
import Submission.Work.CKFinal.LineDecay.model_lam_A0
import Submission.Work.CKFinal.LineDecay.model_lam_A1

namespace Work.CKFinal.LineDecay

open MeasureTheory

/-- **CKMRV's `P₄ ≡ 0`**: for every coefficient function `G`, point `τ` and real `r`, the closed
form `highPart` of the regularised integral `sinSqC r ∫_1^∞ 𝒢(τ,it)e^{-λt}dt` of the cusp model
`𝒢 = Gmodel G τ` equals (minus) the two horizontal segments at height `hsplit = 1`.

NOTE the explicit parentheses around each interval integral: without them the interval-integral
notation swallows the following `-` into the first integrand, and the resulting statement is false.

The four closed forms needed are already proved in this directory: `model_int_left` and
`model_int_right` (the two horizontal integrals, expanded in the basis
`1, z, e^{-2πiz}, z e^{-2πiz}`) and `model_lam_A0`, `model_lam_A1` (the two `psi1` identities);
this goal only has to assemble them against the definition of `highPart`. -/
theorem model_identity (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) (r : ℝ) :
    Work.Asymptotics.highPart G τ r
      + Complex.I * (∫ x in (0 : ℝ)..1,
          Work.CKFinal.Gmodel G τ (((x : ℂ) + (Work.CKFinal.hsplit : ℂ) * Complex.I) - 1)
            * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ)
                * ((x : ℂ) + (Work.CKFinal.hsplit : ℂ) * Complex.I)))
      - Complex.I * (∫ x in (-1 : ℝ)..0,
          Work.CKFinal.Gmodel G τ (((x : ℂ) + (Work.CKFinal.hsplit : ℂ) * Complex.I) + 1)
            * Complex.exp (Complex.I * ((Real.pi * r ^ 2 : ℝ) : ℂ)
                * ((x : ℂ) + (Work.CKFinal.hsplit : ℂ) * Complex.I))) = 0 := by
  -- The two scalar identities `i·A₀ = -k·psi1` and `i·A₁ = -i·psi1·(k+1)`, unfolded to the
  -- `QA/QB/PA/PB` basis so that `ring` can combine them.
  have h0l : Complex.I * (QA (Real.pi * r ^ 2) - QB (Real.pi * r ^ 2))
      = -(((Real.pi * r ^ 2 : ℝ) : ℂ)) * (Work.Asymptotics.psi1 (Real.pi * r ^ 2) : ℂ) :=
    model_lam_A0 _
  have h1l : Complex.I * (PA (Real.pi * r ^ 2) - PB (Real.pi * r ^ 2))
      = -Complex.I * (Work.Asymptotics.psi1 (Real.pi * r ^ 2) : ℂ)
          * (((Real.pi * r ^ 2 : ℝ) : ℂ) + 1) :=
    model_lam_A1 _
  have h0m : Complex.I * (QA (Real.pi * r ^ 2 - 2 * Real.pi)
        - QB (Real.pi * r ^ 2 - 2 * Real.pi))
      = -(((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ))
          * (Work.Asymptotics.psi1 (Real.pi * r ^ 2 - 2 * Real.pi) : ℂ) :=
    model_lam_A0 _
  have h1m : Complex.I * (PA (Real.pi * r ^ 2 - 2 * Real.pi)
        - PB (Real.pi * r ^ 2 - 2 * Real.pi))
      = -Complex.I * (Work.Asymptotics.psi1 (Real.pi * r ^ 2 - 2 * Real.pi) : ℂ)
          * (((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ) + 1) :=
    model_lam_A1 _
  rw [model_int_right G τ r, model_int_left G τ r]
  simp only [Work.Asymptotics.highPart]
  linear_combination
    (Complex.exp (-(((Real.pi * r ^ 2 : ℝ) : ℂ))) * G 0 0 τ) * h0l
    + (Complex.exp (-(((Real.pi * r ^ 2 : ℝ) : ℂ))) * G 0 1 τ) * h1l
    + (Complex.exp (-(((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ))) * G 1 0 τ) * h0m
    + (Complex.exp (-(((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ))) * G 1 1 τ) * h1m

end Work.CKFinal.LineDecay
