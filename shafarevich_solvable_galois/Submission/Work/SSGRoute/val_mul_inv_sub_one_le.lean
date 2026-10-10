import Mathlib.RingTheory.Valuation.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- For a valuation `v` with values in `WithZero (Multiplicative ℤ)`, if `v (b - a) < v b * δ`
with `δ ≤ 1`, then `a` and `b` have the same valuation and consequently
`v (b * a⁻¹ - 1) ≤ δ`.  Indeed `v (b - a) < v b * δ ≤ v b` forces `v a = v b`, and
`b * a⁻¹ - 1 = (b - a) * a⁻¹`. -/
lemma val_mul_inv_sub_one_le {κ : Type*} [Field κ] (v : Valuation κ (WithZero (Multiplicative ℤ)))
    {a b : κ} {δ : WithZero (Multiplicative ℤ)} (hb : v b ≠ 0) (hδ : δ ≤ 1)
    (h : v (b - a) < v b * δ) :
    v (b * a⁻¹ - 1) ≤ δ := by
  have hb_pos : 0 < v b := lt_of_le_of_ne zero_le (Ne.symm hb)
  -- `v (b - a) < v b` since `δ ≤ 1`.
  have hmul_le : v b * δ ≤ v b := by
    calc v b * δ ≤ v b * 1 := mul_le_mul_of_nonneg_left hδ zero_le
      _ = v b := mul_one _
  have hlt : v (b - a) < v b := lt_of_lt_of_le h hmul_le
  -- `a ≠ 0`, otherwise `v (b - a) = v b`.
  have ha0 : a ≠ 0 := by
    intro ha
    rw [ha, sub_zero] at hlt
    exact lt_irrefl _ hlt
  -- Hence `a` and `b` have the same valuation.
  have hva : v a = v b := by
    exact Valuation.map_eq_of_sub_lt v (by rwa [Valuation.map_sub_swap])
  -- Multiply the hypothesis by `(v b)⁻¹`.
  have key : v (b - a) * (v b)⁻¹ ≤ δ := by
    have h2 : (v b * δ) * (v b)⁻¹ = δ := by
      rw [mul_assoc, mul_comm δ (v b)⁻¹, ← mul_assoc, mul_inv_cancel₀ hb, one_mul]
    have h1 : v (b - a) * (v b)⁻¹ < (v b * δ) * (v b)⁻¹ :=
      mul_lt_mul_of_pos_right h (inv_pos.mpr hb_pos)
    rw [h2] at h1
    exact le_of_lt h1
  calc
    v (b * a⁻¹ - 1) = v ((b - a) * a⁻¹) := by
      congr 1
      rw [sub_mul, mul_inv_cancel₀ ha0]
    _ = v (b - a) * (v a)⁻¹ := by rw [Valuation.map_mul, map_inv₀]
    _ = v (b - a) * (v b)⁻¹ := by rw [hva]
    _ ≤ δ := key

end Work.SSGRoute
