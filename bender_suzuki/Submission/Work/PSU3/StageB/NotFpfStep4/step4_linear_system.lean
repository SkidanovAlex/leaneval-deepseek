import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB.NotFpfStep4

/-- In a field of characteristic `2`, the linear system
`ζ * Y = e * Z + w`, `f * Y = ζ⁻¹ * Z + w` has the unique solution
`Y = (1 + e * ζ) / (ζ * (1 + e * f)) * w`, `Z = ζ * (f * Y + w)`. -/
theorem step4_linear_system {K : Type} [Field K] [CharP K 2] {ζ e f w Y Z : K}
    (hζ : ζ ≠ 0) (hdet : 1 + e * f ≠ 0)
    (h1 : ζ * Y = e * Z + w) (h2 : f * Y = ζ⁻¹ * Z + w) :
    Y = (1 + e * ζ) / (ζ * (1 + e * f)) * w ∧ Z = ζ * (f * Y + w)
  := by
  -- Multiply the second equation by `ζ` to clear the inverse `ζ⁻¹`.
  have h2z : ζ * (f * Y) = Z + ζ * w := by
    have h := congrArg (fun t => ζ * t) h2
    rw [mul_add] at h
    have hζinv : ζ * (ζ⁻¹ * Z) = Z := by
      rw [← mul_assoc, mul_inv_cancel₀ hζ, one_mul]
    rw [hζinv] at h
    exact h
  -- Hence `Z = ζ * (f * Y + w)` (using `-x = x` in characteristic `2`).
  have hZ : Z = ζ * (f * Y + w) := by
    rw [mul_add, h2z, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  -- Rewrite the first equation in additive form.
  have h1add : ζ * Y + e * Z + w = 0 := by
    have key : e * Z + w + e * Z + w = (e * Z + e * Z) + (w + w) := by ring
    rw [h1, key, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, zero_add]
  rw [hZ] at h1add
  -- This yields `ζ * Y * (1 + e * f) = (1 + e * ζ) * w`.
  have hKey : ζ * Y * (1 + e * f) = (1 + e * ζ) * w := by
    have hg : ζ * Y * (1 + e * f) + (1 + e * ζ) * w = 0 := by
      linear_combination h1add
    have hh := eq_neg_of_add_eq_zero_left hg
    rwa [CharTwo.neg_eq] at hh
  refine ⟨?_, hZ⟩
  rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hζ hdet)]
  linear_combination hKey

end Work.PSU3.StageB.NotFpfStep4
