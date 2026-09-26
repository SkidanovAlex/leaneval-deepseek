import Mathlib
import Submission.Work.Modular.Basic

namespace Work.Modular

open UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm

/-- The transformation formula for the weight-two Eisenstein series under the slash action of
`S : z ↦ -1 / z`:
`E₂(-1/z) = z² E₂(z) - 6 i z / π`. -/
theorem E2_S_smul (z : ℍ) :
    E2 (ModularGroup.S • z) = (z : ℂ) ^ 2 * E2 z - 6 * Complex.I * (z : ℂ) / Real.pi := by
  -- Mathlib's `E2_slash_action` at `γ = S`: `E₂ |[2] S = E₂ - (2 ζ(2))⁻¹ • D₂ S`.
  have h := congrFun (EisensteinSeries.E2_slash_action ModularGroup.S) z
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, one_div,
    ModularForm.SL_slash_apply, ModularGroup.denom_S, EisensteinSeries.D2_S,
    riemannZeta_two] at h
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  -- Multiply the relation by `z ^ 2` to undo the slash automorphy factor `z ^ (-2)`.
  have key1 : (E2 (ModularGroup.S • z) * (z : ℂ) ^ (-2 : ℤ)) * (z : ℂ) ^ 2
      = E2 (ModularGroup.S • z) := by
    rw [zpow_neg, zpow_ofNat, mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hz), mul_one]
  calc E2 (ModularGroup.S • z)
      = (E2 (ModularGroup.S • z) * (z : ℂ) ^ (-2 : ℤ)) * (z : ℂ) ^ 2 := key1.symm
    _ = (E2 z - (2 * ((Real.pi : ℂ) ^ 2 / 6))⁻¹ *
          (2 * (Real.pi : ℂ) * Complex.I / (z : ℂ))) * (z : ℂ) ^ 2 := by rw [h]
    _ = (z : ℂ) ^ 2 * E2 z - 6 * Complex.I * (z : ℂ) / Real.pi := by
        field_simp

end Work.Modular
