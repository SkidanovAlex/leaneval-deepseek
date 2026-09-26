import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.KdevA4
import Submission.Work.Asymptotics.KhatE1Defs
import Submission.Work.Asymptotics.KhatE1Core.Kplus4
import Submission.Work.Asymptotics.KhatE1Core.Kminus4

/-!
# The reduced normal form of `3456π·KdevA4`

`KdevA4` is the `E(z)^4`-coefficient of the sharp funnel residual: its `K₊`-part is
`tailC⁻¹·Phi4`, and its `K₋`-part is `(3456π)⁻¹(b₃ + [Tref8]_{e^4} + [Dev8Sum]_{e^4})`.

Multiplying by `3456π` and using exactly the two substitutions

* `ψ₄ → Φ + P` with `Φ = ψ₄ - ψ₂E₆/E₄`, `P = ψ₂E₆/E₄`, and
* `j(τ)·Φ → E1combo8 - 1152E₄(τ) + 576ψ₄` (the definition of `E1combo8`),

gives the normal form below (`3456π·tailC⁻¹ = -96 i π³` is the scaling of the `K₊`-block; 25 + 14
monomials, terminating).  The surviving atoms are precisely the ones the proved estimates
control: `Φ` (`O(q_τ scale^N)`), `E1combo8` (`E1combo8_bound`), `j(τ)·E1combo8`
(`JmulBig.jmul_big`), `E₁₄(τ)/Δ(τ)`, `P`, and the bounded `E₂, E₄, E₆, j, Xc, z, τ`; the
`j(τ)`-powers are weighted by their accompanying `q_z`-powers (`KhatE1Core.j_mul_qz_lt_one`).
-/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

open Work.Kernels

/-- **The reduced normal form of `KdevA4num = 3456π·KdevA4`.** -/
theorem KdevA4_eq (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane)
    (hΔ : DeltaFun τ ≠ 0) (hE4 : E4Fun τ ≠ 0) :
    Work.Asymptotics.KhatE1Core.KdevA4num ℓ τ z
      =
    - (67392 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * (z : ℂ) * E6Fun τ * (τ : ℂ))
    + (122256 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * E6Fun τ * (6 * Complex.I / (Real.pi : ℂ)) * (τ : ℂ))
    + (834624 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * (z : ℂ) * E4Fun τ * (τ : ℂ) * E2Fun τ)
    - (417312 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * (z : ℂ) * E4Fun τ * (6 * Complex.I / (Real.pi : ℂ)))
    + (744 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * (z : ℂ) * (E14Fun τ / DeltaFun τ) * (τ : ℂ) * E2Fun τ * E2Fun τ)
    - (744 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * (z : ℂ) * (E14Fun τ / DeltaFun τ) * (6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ)
    - (55440 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * (E6Fun τ * (6 * Complex.I / (Real.pi : ℂ)) * (6 * Complex.I / (Real.pi : ℂ)) * (τ : ℂ))
    - (787536 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * E4Fun τ * (6 * Complex.I / (Real.pi : ℂ)) * (τ : ℂ) * E2Fun τ)
    + (393768 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * E4Fun τ * (6 * Complex.I / (Real.pi : ℂ)) * (6 * Complex.I / (Real.pi : ℂ)))
    - (1 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * (z : ℂ) * jInvariantFun τ * (E14Fun τ / DeltaFun τ) * (τ : ℂ) * E2Fun τ * E2Fun τ)
    + (1 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * (z : ℂ) * jInvariantFun τ * (E14Fun τ / DeltaFun τ) * (6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ)
    + (1032 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * (z : ℂ) * E6Fun τ * jInvariantFun τ * (τ : ℂ))
    - (2016 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * E6Fun τ * jInvariantFun τ * (6 * Complex.I / (Real.pi : ℂ)) * (τ : ℂ))
    + (984 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * (E6Fun τ * jInvariantFun τ * (6 * Complex.I / (Real.pi : ℂ)) * (6 * Complex.I / (Real.pi : ℂ)) * (τ : ℂ))
    - (3504 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * (z : ℂ) * E4Fun τ * jInvariantFun τ * (τ : ℂ) * E2Fun τ)
    + (3456 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * E4Fun τ * jInvariantFun τ * (6 * Complex.I / (Real.pi : ℂ)) * (τ : ℂ) * E2Fun τ)
    + (1752 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * (z : ℂ) * E4Fun τ * jInvariantFun τ * (6 * Complex.I / (Real.pi : ℂ)))
    - (1728 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * E4Fun τ * jInvariantFun τ * (6 * Complex.I / (Real.pi : ℂ)) * (6 * Complex.I / (Real.pi : ℂ)))
    - (1 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * (z : ℂ) * E6Fun τ * jInvariantFun τ * jInvariantFun τ * (τ : ℂ))
    + (2 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * E6Fun τ * jInvariantFun τ * jInvariantFun τ * (6 * Complex.I / (Real.pi : ℂ)) * (τ : ℂ))
    - (1 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * (E6Fun τ * jInvariantFun τ * jInvariantFun τ * (6 * Complex.I / (Real.pi : ℂ)) * (6 * Complex.I / (Real.pi : ℂ)) * (τ : ℂ))
    + (2 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * (z : ℂ) * E4Fun τ * jInvariantFun τ * jInvariantFun τ * (τ : ℂ) * E2Fun τ)
    - (2 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * E4Fun τ * jInvariantFun τ * jInvariantFun τ * (6 * Complex.I / (Real.pi : ℂ)) * (τ : ℂ) * E2Fun τ)
    - (1 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * (z : ℂ) * E4Fun τ * jInvariantFun τ * jInvariantFun τ * (6 * Complex.I / (Real.pi : ℂ)))
    + (1 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * E4Fun τ * jInvariantFun τ * jInvariantFun τ * (6 * Complex.I / (Real.pi : ℂ)) * (6 * Complex.I / (Real.pi : ℂ)))
    - (1360862208 : ℂ) * (Work.Asymptotics.Compact.Xc ℓ z * E4Fun τ)
    - (847872 : ℂ) * (Work.Asymptotics.E1combo8 ℓ τ)
    + (1017536256 : ℂ) * (E4Fun τ)
    - (488374272 : ℂ) * (psi4 ℓ τ)
    + (85888512 : ℂ) * ((psi2 ℓ τ * E6Fun τ / E4Fun τ))
    + (85888512 : ℂ) * ((psi4 ℓ τ - psi2 ℓ τ * E6Fun τ / E4Fun τ))
    + (5971968 : ℂ) * (Work.Asymptotics.Compact.Xc ℓ z * E4Fun τ * jInvariantFun τ)
    - (705024 : ℂ) * (E4Fun τ * jInvariantFun τ)
    + (576 : ℂ) * (jInvariantFun τ * Work.Asymptotics.E1combo8 ℓ τ)
    + (331776 : ℂ) * (jInvariantFun τ * psi4 ℓ τ)
    - (1658880 : ℂ) * (jInvariantFun τ * (psi2 ℓ τ * E6Fun τ / E4Fun τ))
    - (3456 : ℂ) * (Work.Asymptotics.Compact.Xc ℓ z * E4Fun τ * jInvariantFun τ * jInvariantFun τ)
    + (1728 : ℂ) * (jInvariantFun τ * jInvariantFun τ * (psi2 ℓ τ * E6Fun τ / E4Fun τ)) := by
  rw [KdevA4num, Kplus4_eq ℓ τ z hΔ hE4, Kminus4_eq ℓ τ z hΔ hE4]
  ring

end

end Work.Asymptotics.KhatE1Core
