import Mathlib

namespace Work.Projection

/-- If `ℓ e = 1` and `A e ≠ 0`, then the endomorphism `w ↦ w + (A w - ℓ w) • e` of a
finite-dimensional real normed space is invertible. -/
lemma isInvertible_one_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (A ℓ : E →L[ℝ] ℝ) (e : E) (hℓ : ℓ e = 1) (hc : A e ≠ 0) :
    (1 + (A - ℓ).smulRight e).IsInvertible := by
  -- The inverse is `w ↦ w + ((ℓ w - A w)/(A e)) • e`; the two identities below are
  -- pure module algebra, using `ℓ e = 1` and `(A e)⁻¹ * (A e) = 1`.
  have key : ∀ w : E,
      (1 + ((A e)⁻¹ • (ℓ - A)).smulRight e) ((1 + (A - ℓ).smulRight e) w) = w := by
    intro w
    simp only [add_apply, one_apply_eq_self, ContinuousLinearMap.smulRight_apply,
      sub_apply, smul_apply, map_add, map_smul, smul_eq_mul]
    rw [hℓ]
    have hk : (A e)⁻¹ * (1 - A e) = (A e)⁻¹ - 1 := by
      rw [mul_sub, mul_one, inv_mul_cancel₀ hc]
    rw [hk]
    have h1 : e + ((A e)⁻¹ - 1) • e = (A e)⁻¹ • e := by
      calc e + ((A e)⁻¹ - 1) • e = (1 : ℝ) • e + ((A e)⁻¹ - 1) • e := by rw [one_smul]
        _ = (1 + ((A e)⁻¹ - 1)) • e := by rw [add_smul]
        _ = (A e)⁻¹ • e := by congr 1; ring
    rw [h1, smul_smul, add_assoc, ← add_smul]
    have hzero : (A e)⁻¹ * (ℓ w - A w) + (A w - ℓ w) * (A e)⁻¹ = 0 := by
      rw [mul_comm (A w - ℓ w) (A e)⁻¹, ← mul_add]; ring
    rw [hzero, zero_smul, add_zero]
  have key2 : ∀ w : E,
      (1 + (A - ℓ).smulRight e) ((1 + ((A e)⁻¹ • (ℓ - A)).smulRight e) w) = w := by
    intro w
    simp only [add_apply, one_apply_eq_self, ContinuousLinearMap.smulRight_apply,
      sub_apply, smul_apply, map_add, map_smul, smul_eq_mul]
    rw [hℓ]
    have h2 : e + (A e - 1) • e = (A e) • e := by
      calc e + (A e - 1) • e = (1 : ℝ) • e + (A e - 1) • e := by rw [one_smul]
        _ = (1 + (A e - 1)) • e := by rw [add_smul]
        _ = (A e) • e := by congr 1; ring
    rw [h2, smul_smul]
    have h3 : (A e)⁻¹ * (ℓ w - A w) * (A e) = ℓ w - A w := by
      rw [mul_assoc, mul_comm (ℓ w - A w) (A e), ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    rw [h3, add_assoc, ← add_smul]
    have h4 : (A w - ℓ w) + (ℓ w - A w) = 0 := by ring
    rw [h4, zero_smul, add_zero]
  exact ⟨ContinuousLinearEquiv.equivOfInverse (1 + (A - ℓ).smulRight e)
    (1 + ((A e)⁻¹ • (ℓ - A)).smulRight e) key key2, rfl⟩

end Work.Projection
