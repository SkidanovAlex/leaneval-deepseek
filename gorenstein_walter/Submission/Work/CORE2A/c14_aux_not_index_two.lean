import Mathlib

namespace Work.CORE2A

/-- A subgroup of index `2` is normal, and every commutator of two elements lies in it
(equivalently, the quotient `G ⧸ N` has order `2`, hence is commutative).  Therefore the
commutator subgroup `⁅G, G⁆` is contained in `N`.  In a perfect group `⁅G, G⁆ = ⊤`, so
`N = ⊤` and `N.index = 1`. -/
theorem c14_aux_not_index_two {G : Type*} [Group G] (h : Group.IsPerfect G) (N : Subgroup G) :
    N.index ≠ 2 := by
  intro hN
  -- Every commutator of two elements of `G` lies in `N`.
  have hle : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro g _ h' _
    -- `g * h' ∈ N ↔ h' * g ∈ N`, both equivalent to `g ∈ N ↔ h' ∈ N`.
    have e1 : g * h' ∈ N ↔ h' * g ∈ N := by
      rw [Subgroup.mul_mem_iff_of_index_two hN, Subgroup.mul_mem_iff_of_index_two hN]
      exact Iff.comm
    -- hence the commutator `(g * h') * (h' * g)⁻¹` lies in `N`.
    have key : (g * h') * (h' * g)⁻¹ ∈ N := by
      rw [Subgroup.mul_mem_iff_of_index_two hN, Subgroup.inv_mem_iff N]
      exact e1
    simpa [commutatorElement_def, mul_inv_rev, mul_assoc] using key
  have hcomm : _root_.commutator G ≤ N := by
    rw [_root_.commutator_def]; exact hle
  -- Perfection forces `N = ⊤`, so `N.index = 1 ≠ 2`.
  have htop : (⊤ : Subgroup G) ≤ N := by
    rw [← h.commutator_eq_top]; exact hcomm
  have hNtop : N = ⊤ := top_le_iff.mp htop
  rw [hNtop] at hN
  simp at hN

end Work.CORE2A
