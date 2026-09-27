import Mathlib

namespace Work.Drive

/-- **The unit square root of a unit complex number near `1`, anchored at `u₀`.**  For unit `u₀` and
unit `Z` with `1 + Z ≠ 0`, the normalisation `u₀ * (1 + Z) / ‖1 + Z‖` is unit and its square is
`u₀ ^ 2 * Z`.  (`Z` is the normalised ratio `z / u₀ ^ 2` in the intended application; the identity
`(1 + Z) ^ 2 / ‖1 + Z‖ ^ 2 = Z` for unit `Z` is the algebraic content.) -/
theorem unit_mul_sq_div (u₀ Z : ℂ) (h0 : ‖u₀‖ = 1) (hZ : ‖Z‖ = 1) (h1 : 1 + Z ≠ 0) :
    (u₀ * (1 + Z) * (((‖1 + Z‖ : ℝ)) : ℂ)⁻¹) ^ 2 = u₀ ^ 2 * Z ∧
    ‖u₀ * (1 + Z) * (((‖1 + Z‖ : ℝ)) : ℂ)⁻¹‖ = 1 := by
  -- The algebraic content: for unit `Z`, `Z * ‖1 + Z‖ ^ 2 = (1 + Z) ^ 2`, i.e.
  -- `(1 + Z) ^ 2 / ‖1 + Z‖ ^ 2 = Z`.
  have hkey : Z * (((‖1 + Z‖ ^ 2 : ℝ)) : ℂ) = (1 + Z)^2 := by
    have hden : (((‖1 + Z‖ ^ 2 : ℝ)) : ℂ) = (1 + Z) * star (1 + Z) := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, Complex.star_def]
    have hZZ : Z * star Z = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hZ]
      norm_num
    rw [hden, show star (1 + Z) = 1 + star Z by simp]
    have h1' : Z * (1 + star Z) = Z + 1 := by rw [mul_add, mul_one, hZZ]
    calc Z * ((1 + Z) * (1 + star Z)) = (1 + Z) * (Z * (1 + star Z)) := by ring
      _ = (1 + Z) * (Z + 1) := by rw [h1']
      _ = (1 + Z)^2 := by ring
  have hrne : (‖1 + Z‖ : ℝ) ≠ 0 := by
    have : ‖1 + Z‖ ≠ 0 := norm_ne_zero_iff.mpr h1
    exact_mod_cast this
  have hdne : (((‖1 + Z‖ ^ 2 : ℝ)) : ℂ) ≠ 0 := by
    have : (‖1 + Z‖ ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 hrne
    exact_mod_cast this
  -- `(↑‖1 + Z‖)⁻¹ ^ 2 = (↑(‖1 + Z‖ ^ 2))⁻¹`.
  have ha2 : ((((‖1 + Z‖ : ℝ)) : ℂ)⁻¹) ^ 2 = ((((‖1 + Z‖ ^ 2 : ℝ)) : ℂ))⁻¹ := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_pow, inv_pow, Complex.ofReal_inv]
  have hZd : (1 + Z)^2 * ((((‖1 + Z‖ ^ 2 : ℝ)) : ℂ))⁻¹ = Z := by
    rw [← hkey, mul_assoc, mul_inv_cancel₀ hdne, mul_one]
  constructor
  · calc (u₀ * (1 + Z) * (((‖1 + Z‖ : ℝ)) : ℂ)⁻¹) ^ 2
        = u₀ ^ 2 * ((1 + Z)^2 * ((((‖1 + Z‖ : ℝ)) : ℂ)⁻¹) ^ 2) := by ring
      _ = u₀ ^ 2 * ((1 + Z)^2 * ((((‖1 + Z‖ ^ 2 : ℝ)) : ℂ))⁻¹) := by rw [ha2]
      _ = u₀ ^ 2 * Z := by rw [hZd]
  · rw [norm_mul, norm_mul, h0, one_mul]
    have hr : ‖(((‖1 + Z‖ : ℝ)) : ℂ)⁻¹‖ = (‖1 + Z‖)⁻¹ := by
      rw [norm_inv, show ‖(((‖1 + Z‖ : ℝ)) : ℂ)‖ = |(‖1 + Z‖ : ℝ)| by simp,
        abs_of_nonneg (norm_nonneg _)]
    rw [hr]
    exact mul_inv_cancel₀ (norm_ne_zero_iff.mpr h1)

end Work.Drive
