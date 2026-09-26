import Mathlib
import Submission.Work.FunctionalEquations.Basic

/-!
# The coefficient functions of the Fourier expansions of `F` and `F̃`

The paper's proof of Theorem 3.1 (Steps 1--2) shows that the generating functions expand as

`F(τ,x) = ∑_{m≥1} a_m(x) e^{2πimτ} + 2πiτ ∑_{m≥1} √(2m) b_m(x) e^{2πimτ}`

and likewise for `F̃`, with coefficients given by the contour integrals over one period
(equations (3.2)/(3.3) of the paper)

`a_m(x) = ∫_{-1+iy}^{iy} (F(τ,x) - τ(F(τ+1,x) - F(τ,x))) e^{-2πimτ} dτ`,
`b_m(x) = (2πi√(2m))^{-1} ∫_{-1+iy}^{iy} (F(τ+1,x) - F(τ,x)) e^{-2πimτ} dτ`.

Since the integrands are 1-periodic in `τ`, the integral over the horizontal segment
`[-1+iy, iy]` equals the integral over `[iy, 1+iy]`, which is parametrized here by
`u ∈ [0,1] ↦ u + i` at the fixed height `y = 1`.  These are the definitions used
throughout the area; `Work.FunctionalEquations.ExpansionFromFunctionalEquations` shows that
the (existential) coefficients of the expansions agree with them.
-/

namespace Work.FE

open LeanEval.Analysis.CKMRVInterpolation
open Work.Core
open scoped FourierTransform SchwartzMap

noncomputable section

/-- The kernel of the contour integral for the `a`-coefficients:
`A(τ,x) = F(τ,x) - τ(F(τ+1,x) - F(τ,x))`. -/
def aKernel {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n) (u : ℝ) (x : E n) : ℂ :=
  S.F ((u : ℂ) + Complex.I) x
    - ((u : ℂ) + Complex.I) * (S.F ((u : ℂ) + Complex.I + 1) x - S.F ((u : ℂ) + Complex.I) x)

/-- The kernel of the contour integral for the `b`-coefficients:
`B(τ,x) = F(τ+1,x) - F(τ,x)`. -/
def bKernel {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n) (u : ℝ) (x : E n) : ℂ :=
  S.F ((u : ℂ) + Complex.I + 1) x - S.F ((u : ℂ) + Complex.I) x

/-- The `m`-th coefficient `a_m(x)` of the expansion of `F`: the contour integral of
`A(τ,x) e^{-2πimτ}` over one period at height `1`. -/
def aCoeff {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (m : Set.Ici (1 : ℕ)) (x : E n) : ℂ :=
  ∫ u in (0 : ℝ)..1, aKernel S u x
    * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℂ) * ((u : ℂ) + Complex.I)))

/-- The `m`-th coefficient `b_m(x)` of the expansion of `F`: the contour integral of
`B(τ,x) e^{-2πimτ}` over one period at height `1`, divided by `2πi√(2m)`. -/
def bCoeff {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (m : Set.Ici (1 : ℕ)) (x : E n) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I * (rate m.1 : ℂ))⁻¹ *
    ∫ u in (0 : ℝ)..1, bKernel S u x
      * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℂ) * ((u : ℂ) + Complex.I)))

/-- The `m`-th coefficient `ã_m(x)` of the expansion of `F̃`. -/
def aTildeCoeff {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (m : Set.Ici (1 : ℕ)) (x : E n) : ℂ :=
  ∫ u in (0 : ℝ)..1,
    (S.Ftilde ((u : ℂ) + Complex.I) x
        - ((u : ℂ) + Complex.I)
          * (S.Ftilde ((u : ℂ) + Complex.I + 1) x - S.Ftilde ((u : ℂ) + Complex.I) x))
      * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℂ) * ((u : ℂ) + Complex.I)))

/-- The `m`-th coefficient `b̃_m(x)` of the expansion of `F̃`. -/
def bTildeCoeff {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (m : Set.Ici (1 : ℕ)) (x : E n) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I * (rate m.1 : ℂ))⁻¹ *
    ∫ u in (0 : ℝ)..1, (S.Ftilde ((u : ℂ) + Complex.I + 1) x - S.Ftilde ((u : ℂ) + Complex.I) x)
      * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℂ) * ((u : ℂ) + Complex.I)))

end

end Work.FE
