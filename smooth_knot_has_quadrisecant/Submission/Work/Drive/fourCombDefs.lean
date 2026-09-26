import Mathlib
import Submission.Work.Drive.jetDefs

/-!
# The complex-polynomial model of the degree-`≤ 4` trigonometric family

`trigBasis : Fin 9 → ℝ → ℝ` is `(1, cos t, sin t, …, cos 4t, sin 4t)`.  Every degree-`≤ 4`
trigonometric polynomial `f` can be written as `f t = z ^ (-4) * Q z` with `z = exp (t * I)` and
`Q` a polynomial of degree at most `8`; this module records the polynomial `fcPoly j` attached
to the `j`-th basis function and the induced linear map `fcGamma` on the coefficient space.

Both are used to prove that the eight functionals "value at `tᵢ`" and "derivative at `tᵢ`"
(`i : Fin 4`, the `tᵢ` distinct modulo the period) are linearly independent on the degree-`≤ 4`
trigonometric polynomials.

Main facts (stated here, proved in the companion modules):
* `trigPoly_eval`: `(fcPoly j).eval (jetExp t) = (jetExp t) ^ 4 * trigBasis j t`;
* `trigGamma_injective`: `fcGamma` is injective;
* `trigGamma_derivative`: `fcGamma (fcDMat y) = I * X * (fcGamma y)' - 4 * I * fcGamma y`,
  where `fcDMat` is the coefficient map induced by differentiation.
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-- The polynomial of degree at most `8` attached to the `j`-th trigonometric basis function:
the unique such polynomial with `(fcPoly j).eval (jetExp t) = (jetExp t) ^ 4 * trigBasis j t`. -/
def fcPoly : Fin 9 → Polynomial ℂ
  | 0 => Polynomial.X ^ 4
  | 1 => Polynomial.C (1 / 2) * (Polynomial.X ^ 5 + Polynomial.X ^ 3)
  | 2 => Polynomial.C ((2 * Complex.I)⁻¹) * (Polynomial.X ^ 5 - Polynomial.X ^ 3)
  | 3 => Polynomial.C (1 / 2) * (Polynomial.X ^ 6 + Polynomial.X ^ 2)
  | 4 => Polynomial.C ((2 * Complex.I)⁻¹) * (Polynomial.X ^ 6 - Polynomial.X ^ 2)
  | 5 => Polynomial.C (1 / 2) * (Polynomial.X ^ 7 + Polynomial.X)
  | 6 => Polynomial.C ((2 * Complex.I)⁻¹) * (Polynomial.X ^ 7 - Polynomial.X)
  | 7 => Polynomial.C (1 / 2) * (Polynomial.X ^ 8 + 1)
  | _ => Polynomial.C ((2 * Complex.I)⁻¹) * (Polynomial.X ^ 8 - 1)

/-- The polynomial model of the coefficient space: the `ℂ`-linear map sending the `j`-th
coefficient to `fcPoly j`. -/
def fcGamma : (Fin 9 → ℂ) →ₗ[ℂ] Polynomial ℂ :=
  ∑ j : Fin 9, (LinearMap.proj j).smulRight (fcPoly j)

theorem trigGamma_apply (y : Fin 9 → ℂ) :
    fcGamma y = ∑ j : Fin 9, y j • fcPoly j := by
  simp only [fcGamma, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]

/-- The coefficient-space map induced by differentiation of the trigonometric family:
`(fcDMat y) j` are the coefficients of the derivative of `∑ j, trigBasis j · y j`. -/
def fcDMat : (Fin 9 → ℂ) →ₗ[ℂ] (Fin 9 → ℂ) :=
  LinearMap.pi fun j : Fin 9 =>
    match j with
    | 0 => 0
    | 1 => -LinearMap.proj 2
    | 2 => LinearMap.proj 1
    | 3 => (-2 : ℂ) • LinearMap.proj 4
    | 4 => (2 : ℂ) • LinearMap.proj 3
    | 5 => (-3 : ℂ) • LinearMap.proj 6
    | 6 => (3 : ℂ) • LinearMap.proj 5
    | 7 => (-4 : ℂ) • LinearMap.proj 8
    | _ => (4 : ℂ) • LinearMap.proj 7

end

end Work.Drive
