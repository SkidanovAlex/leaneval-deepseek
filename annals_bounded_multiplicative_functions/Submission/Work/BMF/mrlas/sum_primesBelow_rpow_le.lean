import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mrlas

theorem sum_primesBelow_rpow_le (σ : ℝ) (hσ : 1 < σ) (N : ℕ) :
    ∑ p ∈ N.primesBelow, (p : ℝ) ^ (-σ) ≤ ∑' n : ℕ, (n : ℝ) ^ (-σ) := by
  refine Summable.sum_le_tsum (N.primesBelow) ?_ ?_
  · intro i _
    exact Real.rpow_nonneg (Nat.cast_nonneg i) _
  · rw [Real.summable_nat_rpow]
    linarith

end Work.BMF.mrlas
