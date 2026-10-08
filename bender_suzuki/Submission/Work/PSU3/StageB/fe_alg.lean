import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB

theorem fe_alg {F : Type*} [Field F] [CharP F 2] {c ā Ab Ua Ub x : F}
    (hc : c ≠ 0) (hā : ā ≠ 0) (hx : x ≠ 0)
    (h1 : (1 + c * ā ^ 2) * Ua = c * x)
    (h2 : (1 + c * Ab) * Ub = c * x)
    (h3 : Ua = (ā⁻¹) ^ 2 * c * Ub) :
    Ab = c + c⁻¹ + (ā⁻¹) ^ 2 := by
  -- In characteristic 2, `1 + 1 = 0`.
  have hchar : (1 : F) + 1 = 0 := by
    have h : ((2 : ℕ) : F) = 0 := CharP.cast_eq_zero F 2
    rw [show ((2 : ℕ) : F) = (1 : F) + 1 from by norm_num] at h
    exact h
  -- `c * x ≠ 0`, hence `Ub ≠ 0` from `h2`.
  have hcx : c * x ≠ 0 := mul_ne_zero hc hx
  have hUb : Ub ≠ 0 := by
    intro h
    rw [h, mul_zero] at h2
    exact hcx h2.symm
  -- Combine `h1` and `h2`, substitute `h3`, and cancel `Ub`.
  have hkey : (1 + c * ā ^ 2) * Ua = (1 + c * Ab) * Ub := h1.trans h2.symm
  rw [h3] at hkey
  have hcancel : (1 + c * ā ^ 2) * ((ā⁻¹) ^ 2 * c) = 1 + c * Ab := by
    have hUb' : ((1 + c * ā ^ 2) * ((ā⁻¹) ^ 2 * c)) * Ub = (1 + c * Ab) * Ub := by
      rw [← hkey]; ring
    exact mul_right_cancel₀ hUb hUb'
  -- Evaluate the left-hand side of `hcancel`.
  have hXval : (1 + c * ā ^ 2) * ((ā⁻¹) ^ 2 * c) = c ^ 2 + c * (ā⁻¹) ^ 2 := by
    field_simp
    ring
  have key : 1 + c * Ab = c ^ 2 + c * (ā⁻¹) ^ 2 := hcancel.symm.trans hXval
  -- Multiply the goal through by `c` and cancel.
  apply mul_left_cancel₀ hc
  have hR : c * (c + c⁻¹ + (ā⁻¹) ^ 2) = c ^ 2 + 1 + c * (ā⁻¹) ^ 2 := by
    field_simp
  have key2 : c * Ab = c ^ 2 + 1 + c * (ā⁻¹) ^ 2 := by
    have h1' := congrArg (fun t => 1 + t) key
    rw [← add_assoc, hchar, zero_add] at h1'
    rw [h1']
    ring
  rw [hR, key2]

end Work.PSU3.StageB
