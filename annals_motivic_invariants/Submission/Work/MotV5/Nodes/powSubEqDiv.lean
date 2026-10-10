import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5.Nodes

theorem powSubEqDiv {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {t a b : Γ} {i j : ℕ}
    (ht : t ≠ 0) (hb : b ≠ 0) (hij : i ≤ j) (h : a * t ^ i = b * t ^ j) :
    t ^ (j - i) = a / b := by
  calc t ^ (j - i) = t ^ j / t ^ i := by rw [pow_sub₀ t ht hij, div_eq_mul_inv]
    _ = (b * t ^ j) / (b * t ^ i) := (mul_div_mul_left _ _ hb).symm
    _ = (a * t ^ i) / (b * t ^ i) := by rw [← h]
    _ = a / b := mul_div_mul_right a b (pow_ne_zero i ht)

end Work.MotV5.Nodes
