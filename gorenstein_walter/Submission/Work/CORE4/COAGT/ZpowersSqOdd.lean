import Mathlib

namespace Work.CORE4.COAGT

/-- If `g` has odd order then `g` and `g ^ 2` generate the same cyclic subgroup. -/
theorem ZpowersSqOdd {G : Type*} [Group G] (g : G) (h : Odd (orderOf g)) :
    Subgroup.zpowers (g ^ 2) = Subgroup.zpowers g := by
  obtain ⟨k, hk⟩ := h
  apply le_antisymm
  · rw [Subgroup.zpowers_le]
    exact Subgroup.pow_mem (Subgroup.zpowers g) (Subgroup.mem_zpowers g) 2
  · rw [Subgroup.zpowers_le, Subgroup.mem_zpowers_iff]
    refine ⟨-(k : ℤ), ?_⟩
    have h1 : g ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one g
    have h2 : g * (g ^ 2) ^ k = 1 := by
      rw [← pow_mul, ← pow_succ']
      exact h1
    rw [zpow_neg, zpow_natCast, eq_inv_of_mul_eq_one_right h2, inv_inv]

end Work.CORE4.COAGT
