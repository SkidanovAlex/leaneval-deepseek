import Mathlib
import Submission.Work.Asymptotics.KhatE1Defs
import Submission.Work.Asymptotics.KhatE1Core.KdevA4
import Submission.Work.Asymptotics.Compact.kminus_tail_core

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

noncomputable section

open Work.Kernels

/-!
# The `E(z)^5`-coefficient `KdevA5` of the sharp funnel residual

Writing `e = Ept z` and `Wres = Kdev8Bracket - 2·KdevE2·e²`, the residual has the expansion
`Wres = Σ_{k≥3} a_k e^k` with `a_k` a polynomial in `z` of degree at most two.  Its `e⁵`-coefficient
is (because `Φ₁+Φ₂+Φ₃` is a function of `q(z) = e²`, so has no `e⁵`-term)

  `a₅ = (3456π)⁻¹·(R8_p4 + [Dev8Sum]_{e⁵})`,  `[Dev8Sum]_{e⁵} = γ·β₁ + [Dev8Raw]_{e⁵} + (j-720)·[Dev8Raw]_{e³}`

with `γ = (j(τ)-720)² - 179280 - 24j(τ)`, `β₁ = [br8ref]_{e^1} = R8_p0 = 24·E1combo8`
(`[dSinv]_{e^4} = γ` and `[br8ref]_{e^1} = 24·E1combo8` are the proved second-order identities), and

* `[Dev8Raw]_{e³} = 36864·E₄(τ) - 480·P - 55296·ψ₄ + 480·j·ψ₄`  (`P = ψ₂E₁₄/Δ`),
* `[Dev8Raw]_{e⁵} = -3456(dL₅ - 264dL₃)E₄(τ) - 3456·(-8)dE10₄·E₄(τ)
      + P·(dW₅ + 480dW₃ - dD2₅ + 504dD2₃) + P·(-8dE8₄ - 16dE6₄)
      + ψ₄·((1728-j)(dW₅+480dW₃) + j(dD2₅-504dD2₃)) + ψ₄·((1728-j)(-8dE8₄) + j(16dE6₄))`

where the exact deviation coefficients are (from the theta series, verified numerically)

  `dL₃ = -32/3`, `dL₅ = -48/5`, `dW₃ = -32`, `dW₅ = -48`, `dD2₃ = 448`, `dD2₅ = 2016`,
  `dE8₄ = 61920`, `dE6₄ = -16632`, `dE10₄ = -135432`.

Numerical check: at `τ = 4i`, `z = 0.5+5i` this gives `a₅ = -6.469e-4`, matching the independently
measured value of `.kdevdir/NOTES.md` (session 3: `a₅ ≈ -6.5e-4`); `a₅` is `z`-independent
(like `a₃`).
-/

/-- `P = ψ₂(τ)·E₁₄(τ)/Δ(τ)` (the `Q`-monomial of the `K₋`-bracket). -/
def psi2E14oD (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  psi2 ℓ τ * E14Fun τ / DeltaFun τ

/-- The `e³`-coefficient of `Dev8Raw`. -/
def Dev8Raw3 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  36864 * E4Fun τ - 480 * psi2E14oD ℓ τ
    + (-55296 + 480 * jInvariantFun τ) * psi4 ℓ τ

/-- The `e⁵`-coefficient of `Dev8Raw`. -/
def Dev8Raw5 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  - (18770614272 : ℂ) / 5 * E4Fun τ
    - 20880 * psi2E14oD ℓ τ
    - 882607104 * psi4 ℓ τ
    + 20880 * (jInvariantFun τ * psi4 ℓ τ)

/-- The `e⁵`-coefficient `KdevA5 = [Wres]_{e^5}` of the sharp funnel residual. -/
def KdevA5 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ *
    ( Work.Asymptotics.Compact.R8_p4 ℓ τ
      + (((jInvariantFun τ - 720) ^ 2 - 179280 - 24 * jInvariantFun τ)
          * (24 * Work.Asymptotics.E1combo8 ℓ τ))
      + Dev8Raw5 ℓ τ z
      + (jInvariantFun τ - 720) * Dev8Raw3 ℓ τ z )

end

end Work.Asymptotics.KhatE1
