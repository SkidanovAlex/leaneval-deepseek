import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

theorem bikeSet_arith (ℓ : ℕ) {c p1 p2 N C1 : ℝ} (hN : N ≠ 0) (hC1 : C1 ≠ 0) (hp2 : p2 ≠ 0) :
    1 / (2 * C1 ^ (2 * ℓ)) * c ^ (4 * ℓ + 2) * p2 * (p1 ^ 2) ^ (2 * ℓ + 1) / N
      = (c ^ 2 * p2 * p1 ^ 2 * N) ^ (2 * ℓ + 1) / (2 * (C1 * p2) ^ (2 * ℓ) * N ^ (2 * ℓ + 2)) := by
  field_simp
  ring

end Work.BMF
