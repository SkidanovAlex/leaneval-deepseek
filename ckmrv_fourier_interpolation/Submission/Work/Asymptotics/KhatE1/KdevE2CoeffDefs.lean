import Mathlib
import Submission.Work.Asymptotics.KhatE1.KdevE2Defs

/-!
# The `z`-polynomial coefficients of the `E(z)²`-coefficient `KdevE2`

`KdevE2 ℓ τ z` is a polynomial of degree `2` in `z`, with `τ`-dependent coefficients
`KdevE2c2`, `KdevE2c1`, `KdevE2c0`.  The identities of this file decompose the bound of
`KdevE2fun_funnel` into the three coefficient bounds.
-/

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

noncomputable section

/-- The `z²`-coefficient of `KdevE2`. -/
noncomputable def KdevE2c2 (τ : UpperHalfPlane) : ℂ :=
  (1 / (2 * Work.Asymptotics.Compact.tailC)) *
    (48 * (τ : ℂ) * Work.Kernels.E6Fun τ - 48 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ
      - Work.Kernels.phi2 τ * Work.Kernels.E14Fun τ / Work.Kernels.DeltaFun τ
      - ((τ : ℂ) * Work.Kernels.E6Fun τ * (Work.Kernels.jInvariantFun τ - 240)
          - 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ
              * (Work.Kernels.jInvariantFun τ - 984)))

/-- The `z¹`-coefficient of `KdevE2`. -/
noncomputable def KdevE2c1 (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  (1 / (2 * Work.Asymptotics.Compact.tailC)) *
    ( -24 * ((τ : ℂ) * Work.Kernels.E6Fun τ * (12 * Complex.I / (Real.pi : ℂ)))
      - ((τ : ℂ) * Work.Kernels.E6Fun τ * (-(12 * Complex.I) / (Real.pi : ℂ))
            * (Work.Kernels.jInvariantFun τ - 240)
          - 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ
              * (-(6 * Complex.I) / (Real.pi : ℂ))
              * (Work.Kernels.jInvariantFun τ - 984)) )
  + (1 / (6912 * (Real.pi : ℂ))) *
      ((Real.pi : ℂ) * Complex.I
        * (3400704 * Work.Kernels.E4Fun τ
            - 3456 * Work.Kernels.jInvariantFun τ * Work.Kernels.E4Fun τ))

/-- The `z⁰`-coefficient of `KdevE2`. -/
noncomputable def KdevE2c0 (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  (1 / (2 * Work.Asymptotics.Compact.tailC)) *
    ( - ((τ : ℂ) * Work.Kernels.E6Fun τ * (-(36 : ℂ) / (Real.pi : ℂ) ^ 2)
          * (Work.Kernels.jInvariantFun τ - 240)) )
  + (1 / (6912 * (Real.pi : ℂ))) *
      (Work.Asymptotics.Compact.cuspC ℓ
          * (3400704 * Work.Kernels.E4Fun τ
              - 3456 * Work.Kernels.jInvariantFun τ * Work.Kernels.E4Fun τ)
        + (-41472 * Work.Kernels.E4Fun τ - 373248 * Work.Kernels.psi4 ℓ τ
            + 1152 * (Work.Kernels.psi2 ℓ τ * Work.Kernels.E14Fun τ
                / Work.Kernels.DeltaFun τ)
            + 576 * Work.Kernels.jInvariantFun τ * Work.Kernels.psi4 ℓ τ))

/-- **The `z`-polynomial decomposition of `KdevE2`.** -/
theorem KdevE2_eq_poly (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) :
    KdevE2 ℓ τ z
      = KdevE2c2 τ * (z : ℂ) ^ 2 + KdevE2c1 ℓ τ * (z : ℂ) + KdevE2c0 ℓ τ := by
  rw [KdevE2, KdevE2plus, KdevE2minus, KdevE2c2, KdevE2c1, KdevE2c0,
    Work.Asymptotics.Compact.Xc]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The ``cleared'' form of the `z⁰`-coefficient: `2π Δ · KdevE2c0` is the polynomial

`-πiτE₆E₄³ - cuspC·E₄⁴ + E₄³ψ₄/6 + E₁₄ψ₂/3 + Δ(240πiτE₆ + (984·cuspC - 12)E₄ - 108ψ₄)`

(no `j`, no `ψ`-denominators). -/
noncomputable def KdevE2expr (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  - ((Real.pi : ℂ) * Complex.I * (τ : ℂ)) * Work.Kernels.E6Fun τ * Work.Kernels.E4Fun τ ^ 3
  - Work.Asymptotics.Compact.cuspC ℓ * Work.Kernels.E4Fun τ ^ 4
  + Work.Kernels.E4Fun τ ^ 3 * Work.Kernels.psi4 ℓ τ / 6
  + (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ) * Work.Kernels.psi2 ℓ τ / 3
  + Work.Kernels.DeltaFun τ *
      (240 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) * Work.Kernels.E6Fun τ
        + (984 * Work.Asymptotics.Compact.cuspC ℓ - 12) * Work.Kernels.E4Fun τ
        - 108 * Work.Kernels.psi4 ℓ τ)

/-- **The cleared `z⁰`-identity**: `2π Δ · KdevE2c0 = KdevE2expr`. -/
theorem KdevE2expr_eq (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) :
    2 * (Real.pi : ℂ) * Work.Kernels.DeltaFun τ * KdevE2c0 ℓ τ = KdevE2expr ℓ τ := by
  have hD : Work.Kernels.DeltaFun τ ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  have hj : Work.Kernels.DeltaFun τ * Work.Kernels.jInvariantFun τ
      = Work.Kernels.E4Fun τ ^ 3 := Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun τ
  rw [KdevE2c0, KdevE2expr, Work.Asymptotics.Compact.tailC]
  rw [show Work.Kernels.jInvariantFun τ = Work.Kernels.E4Fun τ ^ 3 / Work.Kernels.DeltaFun τ
      from rfl]
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

end

end Work.Asymptotics.KhatE1
