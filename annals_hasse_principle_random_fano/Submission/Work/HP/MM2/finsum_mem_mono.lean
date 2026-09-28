import Mathlib

open scoped BigOperators

namespace Work.HP.MM2

theorem finsum_mem_mono {α : Type*} {S : Set α} (hS : S.Finite) {f g : α → ℝ}
    (h : ∀ p ∈ S, f p ≤ g p) : (∑ᶠ p ∈ S, f p) ≤ ∑ᶠ p ∈ S, g p := by
  rw [← hS.coe_toFinset, finsum_mem_coe_finset, finsum_mem_coe_finset]
  exact Finset.sum_le_sum fun p hp => h p (hS.mem_toFinset.mp hp)

end Work.HP.MM2
