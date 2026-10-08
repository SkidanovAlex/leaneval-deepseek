import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.HardCore

theorem smul_coord_of_det_ne_zero {F : Type*} [Field F] (u v w : F × F)
    (h : u.1 * v.2 - u.2 * v.1 ≠ 0) :
    ((w.1 * v.2 - w.2 * v.1) / (u.1 * v.2 - u.2 * v.1)) • u +
      ((u.1 * w.2 - u.2 * w.1) / (u.1 * v.2 - u.2 * v.1)) • v = w := by
  have h' : v.2 * u.1 - v.1 * u.2 ≠ 0 := by
    rw [mul_comm v.2 u.1, mul_comm v.1 u.2]
    exact h
  ext <;> simp <;> field_simp [h'] <;> ring

end Work.Hering.HardCore
