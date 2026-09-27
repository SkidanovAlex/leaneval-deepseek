import Mathlib
import Submission.Work.EQ.germ_value_defs

namespace Work.EQ

/-- Scaling the variable: the multiplicity of the root `w` of `P` equals the multiplicity
of the root `w / ℓ` of `P (ℓ ·)`, for `ℓ ≠ 0`.

This is the specialization `a = ℓ`, `b = 0`, `c = w / ℓ` of Mathlib's
`Polynomial.rootMultiplicity_comp_C_mul_X_add_C`. -/
theorem rootMultiplicity_comp_C_mul_X (P : Polynomial ℂ) (w ℓ : ℂ) (hℓ : ℓ ≠ 0) :
    (P.comp (Polynomial.C ℓ * Polynomial.X)).rootMultiplicity (w / ℓ) = P.rootMultiplicity w := by
  have h := Polynomial.rootMultiplicity_comp_C_mul_X_add_C P ℓ 0 (w / ℓ)
    (isUnit_iff_ne_zero.mpr hℓ)
  rw [show Polynomial.C ℓ * Polynomial.X + Polynomial.C 0 = Polynomial.C ℓ * Polynomial.X by
        simp,
    add_zero] at h
  rw [h, div_eq_mul_inv, ← mul_assoc, mul_comm ℓ w, mul_inv_cancel_right₀ hℓ]

end Work.EQ
