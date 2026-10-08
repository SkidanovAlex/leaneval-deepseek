import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageA

/-- Field-algebra lemma used in Case B of the PSU3 analysis.

In a field `F` of characteristic two, given nonzero `a, k₁, k₂, w₁, w₂` satisfying
the three relations `h5, h6, h7` and the normalization inequalities `hx₁, hx₂`,
one must have `k₁ = k₂`.

The proof clears the inverses in `h6` and `h7` to obtain the polynomial relations
`k₂ w₁ = a k₁ w₂` and `a k₁² w₂ + a k₁² k₂ = k₂² w₁ + k₁ k₂²`, combines them with
`h5` into the product identity `(k₁ - k₂) * (w₁ (k₁⁻¹ + 1) + 1) = 0`, and finally
uses that `w₁ (k₁⁻¹ + 1) ≠ 1` together with characteristic two (`-1 = 1`). -/
theorem caseB_field_algebra {F : Type} [Field F] (h2 : (2 : F) = 0)
    {a k₁ k₂ w₁ w₂ : F} (ha : a ≠ 0) (hk₁ : k₁ ≠ 0) (hk₂ : k₂ ≠ 0)
    (hw₁ : w₁ ≠ 0) (hw₂ : w₂ ≠ 0)
    (h5 : 1 + k₂ = a * (1 + k₁))
    (h6 : w₂⁻¹ * k₂ = a * w₁⁻¹ * k₁)
    (h7 : w₂ * (k₂⁻¹) ^ 2 + k₂⁻¹ = a⁻¹ * (w₁ * (k₁⁻¹) ^ 2 + k₁⁻¹))
    (hx₁ : w₁ * (k₁⁻¹ + 1) ≠ 1) (hx₂ : w₂ * (k₂⁻¹ + 1) ≠ 1) :
    k₁ = k₂ := by
  -- Clear denominators in `h6` to get the polynomial relation `k₂ w₁ = a k₁ w₂`.
  have h6' : k₂ * w₁ - a * k₁ * w₂ = 0 := by
    have h := h6
    field_simp at h
    linear_combination h
  -- Clear denominators in `h7`.
  have h7' : a * k₁ ^ 2 * w₂ - k₂ ^ 2 * w₁ + a * k₁ ^ 2 * k₂ - k₁ * k₂ ^ 2 = 0 := by
    have h := h7
    field_simp at h
    linear_combination h
  -- `h5` as a polynomial relation.
  have h5' : 1 + k₂ - a * (1 + k₁) = 0 := by rw [h5, sub_self]
  -- Combine into `Q = (k₁ - k₂) * (w₁ (1 + k₁) + k₁) = 0`.
  have hQ : (k₁ - k₂) * (w₁ * (1 + k₁) + k₁) = 0 := by
    have hk₂Q : k₂ * ((k₁ - k₂) * (w₁ * (1 + k₁) + k₁)) = 0 := by
      linear_combination (1 + k₁) * (k₁ * h6' + h7') + k₁ ^ 2 * k₂ * h5'
    exact (mul_eq_zero.mp hk₂Q).resolve_left hk₂
  -- Relate `w₁ (1 + k₁) + k₁` to `k₁ * (w₁ (k₁⁻¹ + 1) + 1)`.
  have hkX : k₁ * (w₁ * (k₁⁻¹ + 1) + 1) = w₁ * (1 + k₁) + k₁ := by
    field_simp
  -- In characteristic two, `1 = -1`.
  have hneg1 : (1 : F) = -1 := by
    have htwo : (2 : F) = 1 + 1 := by norm_num
    rw [htwo] at h2
    exact eq_neg_iff_add_eq_zero.mpr h2
  -- `w₁ (k₁⁻¹ + 1) + 1 ≠ 0`, from `hx₁` and characteristic two.
  have hX1 : w₁ * (k₁⁻¹ + 1) + 1 ≠ 0 := by
    intro h
    apply hx₁
    exact (eq_neg_of_add_eq_zero_left h).trans hneg1.symm
  -- The product identity.
  have hkey : (k₁ - k₂) * (w₁ * (k₁⁻¹ + 1) + 1) = 0 := by
    have hmul : k₁ * ((k₁ - k₂) * (w₁ * (k₁⁻¹ + 1) + 1)) = 0 := by
      calc k₁ * ((k₁ - k₂) * (w₁ * (k₁⁻¹ + 1) + 1))
          = (k₁ - k₂) * (k₁ * (w₁ * (k₁⁻¹ + 1) + 1)) := by ring
        _ = (k₁ - k₂) * (w₁ * (1 + k₁) + k₁) := by rw [hkX]
        _ = 0 := hQ
    exact (mul_eq_zero.mp hmul).resolve_left hk₁
  exact sub_eq_zero.mp ((mul_eq_zero.mp hkey).resolve_right hX1)

end Work.PSU3.StageA
