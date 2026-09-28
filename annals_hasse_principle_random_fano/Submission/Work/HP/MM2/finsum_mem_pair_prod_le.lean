import Mathlib

namespace Work.HP.MM2

open scoped BigOperators

/-- For a finite subset `u ⊆ s ×ˢ t` and nonnegative functions `F`, `g` on `s`, `t`, the
`finsum` over `u` of the product `F p.1 * g p.2` is at most the product of the sums over `s` and
`t`. -/
theorem finsum_mem_pair_prod_le {ι κ : Type*} {s : Set ι} {t : Set κ} {u : Set (ι × κ)}
    (hs : s.Finite) (ht : t.Finite) (hu : u.Finite) (hsub : u ⊆ s ×ˢ t)
    {F : ι → ℝ} {g : κ → ℝ} (hF : ∀ x ∈ s, 0 ≤ F x) (hg : ∀ y ∈ t, 0 ≤ g y) :
    (∑ᶠ p ∈ u, F p.1 * g p.2) ≤ (∑ᶠ x ∈ s, F x) * (∑ᶠ y ∈ t, g y) := by
  rw [← hu.coe_toFinset, finsum_mem_coe_finset,
      ← hs.coe_toFinset, finsum_mem_coe_finset,
      ← ht.coe_toFinset, finsum_mem_coe_finset]
  have hsub' : hu.toFinset ⊆ hs.toFinset ×ˢ ht.toFinset := by
    rw [Set.Finite.toFinset_subset, Finset.coe_product, hs.coe_toFinset, ht.coe_toFinset]
    exact hsub
  calc ∑ p ∈ hu.toFinset, F p.1 * g p.2
      ≤ ∑ p ∈ hs.toFinset ×ˢ ht.toFinset, F p.1 * g p.2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub'
        intro p hp _
        rw [Finset.mem_product] at hp
        exact mul_nonneg (hF p.1 (hs.mem_toFinset.mp hp.1)) (hg p.2 (ht.mem_toFinset.mp hp.2))
    _ = (∑ x ∈ hs.toFinset, F x) * (∑ y ∈ ht.toFinset, g y) := by
        rw [Finset.sum_product, ← Finset.sum_mul_sum]

end Work.HP.MM2
