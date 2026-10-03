/-
# The first-derivative formula for the oscillatory phase `momFun` (Area A7)

`momFun P ξ₁ ξ₂ t = e(ξ₁t + ξ₂ P(t))` with `e(x) = exp(2πi x)` (see
`Submission/Work/A7/ModelApproxCore_M0_defs.lean`).  Since `momFun` is `Complex.exp ∘ φ` with the
real phase `φ t = ξ₁ t + ξ₂ PevalR P t` and `φ' t = ξ₁ + ξ₂ P'(t)` (`PderivR`, the real evaluation
of `P.derivative`), the chain rule gives

`deriv (momFun P ξ₁ ξ₂) t = momFun P ξ₁ ξ₂ t * (2πi * (ξ₁ + ξ₂ P'(t)))`.

This is the first step of the second-derivative computation of
`Submission/Work/A7/momFun_iteratedDeriv_two_eq.lean` and of the sharp `‖M₀‖` bound of §6.

Route: `Polynomial.hasDerivAt` for the real derivative of `PevalR P` (`hasDerivAt_PevalR`),
`HasDerivAt.ofReal_comp` / `HasDerivAt.const_mul` to pass to `ℂ`, `HasDerivAt.cexp` for the
exponential, and `HasDerivAt.deriv`.
-/
import Mathlib
import Submission.Work.A7.ModelApproxCore_M0_defs
import Submission.Work.KMTPlan.A6.IntegIdent

set_option autoImplicit false

namespace Work.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology

/-- **The chain-rule formula for the first derivative of the oscillatory phase**
`momFun P ξ₁ ξ₂ t = e(ξ₁t + ξ₂ P(t))` (`e(x) = exp(2πi x)`): with the real phase
`φ t = ξ₁t + ξ₂ PevalR P t`, whose derivative is `φ' t = ξ₁ + ξ₂ P'(t)`
(`PderivR P` = the real evaluation of `P.derivative`), one has
`(e^{2πiφ})' = e^{2πiφ} · 2πi · φ'`. -/
theorem momFun_deriv_formula (P : Polynomial ℤ) (ξ₁ ξ₂ : ℝ) (t : ℝ) :
    deriv (Work.A7.momFun P ξ₁ ξ₂) t
      = Work.A7.momFun P ξ₁ ξ₂ t
          * (2 * (Real.pi : ℂ) * Complex.I
              * ((ξ₁ : ℂ) + (ξ₂ : ℂ) * ((Work.KMTPlan.A6.PderivR P t : ℝ) : ℂ))) := by
  -- the real phase and its derivative
  have hφ : HasDerivAt (fun s : ℝ => ξ₁ * s + ξ₂ * Work.KMTAreas.A7.PevalR P s)
      (ξ₁ + ξ₂ * Work.KMTPlan.A6.PderivR P t) t := by
    have h1 : HasDerivAt (fun s : ℝ => ξ₁ * s) ξ₁ t := by
      simpa using hasDerivAt_const_mul (𝕜 := ℝ) (c := ξ₁) (x := t)
    have h2 : HasDerivAt (fun s : ℝ => ξ₂ * Work.KMTAreas.A7.PevalR P s)
        (ξ₂ * Work.KMTPlan.A6.PderivR P t) t :=
      (Work.KMTPlan.A6.hasDerivAt_PevalR P t).const_mul ξ₂
    exact h1.add h2
  -- the complexified phase `s ↦ 2πi · φ s` and its derivative
  have hφC : HasDerivAt
      (fun s : ℝ => ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)
        * ((ξ₁ * s + ξ₂ * Work.KMTAreas.A7.PevalR P s : ℝ) : ℂ))
      (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)
        * (((ξ₁ + ξ₂ * Work.KMTPlan.A6.PderivR P t : ℝ)) : ℂ)) t :=
    hφ.ofReal_comp.const_mul _
  have hExp := hφC.cexp
  -- `momFun` is `Complex.exp` of that phase
  have hfun : Work.A7.momFun P ξ₁ ξ₂
      = fun s : ℝ => Complex.exp (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)
          * ((ξ₁ * s + ξ₂ * Work.KMTAreas.A7.PevalR P s : ℝ) : ℂ)) := rfl
  rw [hfun, hExp.deriv]
  congr 1
  push_cast
  ring

end

end Work.A7
