import Mathlib
import Submission.Work.CDcl.xrel_defs
import Submission.Work.CDcl.xco_ode_P
import Submission.Commons.RingTheory.PowerSeries.subst_injective_of_constantCoeff_zero

/-!
# The coefficient identities of the pulled-back ODE

The pulled-back ODE for `Pw = P∘φ` has coefficients
`dLΨ/Ψ - Ψ·(P₁∘φ)/(P₂∘φ)`, `-Ψ²(P₀∘φ)/(P₂∘φ)`, `Ψ²(p∘φ)/(P₂∘φ)` with `Ψ = φ'`;
using `Ψ = toL(dRat phiK)`, `φ' = -1/(x-1)²`, `φ'' = 2/(x-1)³` they are `toL` of the rational
functions `α̃ = -Q₁/Q₂`, `β̃ = -Q₀/Q₂`, `γ̃ = (p∘φ)/Q₂` of `setup.lean`.

This file proves the nonvanishing facts and the three rational-function identities.
-/

noncomputable section

open Polynomial PowerSeries

namespace Work.CDcl

/-- The power series `sympPhi` is nonzero. -/
theorem sympPhi_ne_zero : Submission.CDT.sympPhi ≠ 0 := by
  intro h
  have h1 := congrArg (PowerSeries.coeff 1) h
  rw [Submission.CDT.coeff_sympPhi_one] at h1
  simp at h1

/-- `P₂(x/(x-1))` is nonzero. -/
theorem p2phiK_ne_zero (a b : ℚ) : p2phiK a b ≠ 0 := by
  intro h
  have hinj := Commons.RingTheory.PowerSeries.subst_injective_of_constantCoeff_zero
    (φ := Submission.CDT.sympPhi)
    (by
      rw [show Submission.CDT.sympPhi
          = (PowerSeries.X : PowerSeries ℚ) * ((PowerSeries.X : PowerSeries ℚ) - 1)⁻¹ from rfl,
        map_mul]
      rw [show PowerSeries.constantCoeff (PowerSeries.X : PowerSeries ℚ) = 0 from by
        rw [show (PowerSeries.X : PowerSeries ℚ) = MvPowerSeries.X () from rfl]
        exact MvPowerSeries.constantCoeff_X ()]
      rw [zero_mul])
    sympPhi_ne_zero
  have h1 : algebraMap (PowerSeries ℚ) LF
      (((p2poly a b : Polynomial ℚ) : PowerSeries ℚ).subst Submission.CDT.sympPhi) = 0 := by
    rw [substPhi_poly (p2poly a b)]
    rw [show ((p2poly a b : Polynomial ℚ).eval₂ (algebraMap ℚ (RatFunc ℚ)) phiK)
        = p2phiK a b from rfl, h, map_zero]
  have hzero : ((0 : PowerSeries ℚ).subst Submission.CDT.sympPhi) = 0 := by
    rw [show (0 : PowerSeries ℚ) = PowerSeries.C (0 : ℚ) from (map_zero PowerSeries.C).symm,
      PowerSeries.subst_C]
    rfl
  have h3 : ((p2poly a b : Polynomial ℚ) : PowerSeries ℚ) = 0 := by
    have h4 : (((p2poly a b : Polynomial ℚ) : PowerSeries ℚ).subst Submission.CDT.sympPhi)
        = ((0 : PowerSeries ℚ).subst Submission.CDT.sympPhi) := by
      rw [algebraMap_eq_zero h1, hzero]
    exact hinj h4
  exact p2poly_ne_zero a b (Polynomial.coe_injective ℚ h3)

/-- `Q₂ ≠ 0`. -/
theorem Q2K_ne_zero (a b : ℚ) : Q2K a b ≠ 0 := by
  rw [show Q2K a b = p2phiK a b * (xK - 1) ^ 4 from rfl]
  exact mul_ne_zero (p2phiK_ne_zero a b) (pow_ne_zero 4 xK_sub_one_ne_zero)

theorem toL_Q2K_ne_zero (a b : ℚ) : toL (Q2K a b) ≠ 0 := by
  intro h
  exact Q2K_ne_zero a b (toL_injective (by rw [h, map_zero]))

set_option maxHeartbeats 800000 in
/-- The `dL Pw` coefficient: `dRat²φ/dRat φ - dRat φ·(P₁∘φ)/(P₂∘φ) = α̃`. -/
theorem coef_alphaKt (a b : ℚ) :
    Submission.CDT.dRat (Submission.CDT.dRat phiK) / Submission.CDT.dRat phiK
      - Submission.CDT.dRat phiK * p1phiK a b / p2phiK a b = alphaKt a b := by
  have hB : p2phiK a b ≠ 0 := p2phiK_ne_zero a b
  rw [dRat2_phiK_val, dRat_phiK_val]
  simp only [alphaKt, Q1K, Q2K]
  field_simp
  ring

set_option maxHeartbeats 800000 in
/-- The `Pw` coefficient: `-dRat φ²·(P₀∘φ)/(P₂∘φ) = β̃`. -/
theorem coef_betaKt (a b : ℚ) :
    -((Submission.CDT.dRat phiK) ^ 2 * p0phiK a b / p2phiK a b) = betaKt a b := by
  have hB : p2phiK a b ≠ 0 := p2phiK_ne_zero a b
  rw [dRat_phiK_val]
  simp only [betaKt, Q0K, Q2K]
  field_simp

set_option maxHeartbeats 800000 in
/-- The constant coefficient: `dRat φ²·(p∘φ)/(P₂∘φ) = γ̃`. -/
theorem coef_gammaKt (a b : ℚ) (ra rb rab r0 : ℤ) :
    (Submission.CDT.dRat phiK) ^ 2 * pphiK a b ra rb rab r0 / p2phiK a b
      = gammaKt a b ra rb rab r0 := by
  have hB : p2phiK a b ≠ 0 := p2phiK_ne_zero a b
  rw [dRat_phiK_val]
  simp only [gammaKt, pphiK, Q2K]
  field_simp

end Work.CDcl
