import Mathlib

namespace Work.CFT.MaxProP.ContCohomology.Burnside

open scoped Pointwise in
/-- In a profinite (compact, totally disconnected) topological group, for any closed
subgroup `K` and any `x ∉ K`, there is an open normal subgroup `N` such that `x ∉ K ⊔ N`.
Equivalently, the image of `x` in the finite quotient `G ⧸ N` avoids the image of `K`. -/
theorem exists_openNormalSubgroup_sup_ne_top {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    {K : Subgroup G} (hK : IsClosed (K : Set G)) {x : G} (hx : x ∉ K) :
    ∃ N : OpenNormalSubgroup G, x ∉ K ⊔ N.toSubgroup := by
  -- The complement of the left coset `x • K` is an open neighborhood of `1`.
  let U : Set G := (x • (K : Set G))ᶜ
  have UOpen : IsOpen U := ((Homeomorph.mulLeft x).isClosedMap _ hK).isOpen_compl
  have einU : 1 ∈ U := by
    refine Set.mem_compl (fun ⟨k, hk, hkx⟩ ↦ ?_)
    simp only [smul_eq_mul] at hkx
    rw [mul_eq_one_iff_eq_inv] at hkx
    exact hx (hkx ▸ inv_mem hk)
  -- Open normal subgroups form a neighborhood basis of `1` in a profinite group.
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one UOpen einU
  refine ⟨N, fun hxN ↦ ?_⟩
  rw [sup_comm] at hxN
  rcases Subgroup.mem_sup_of_normal_left.mp hxN with ⟨n, hn, k, hk, hnk⟩
  rw [← eq_mul_inv_iff_mul_eq] at hnk
  -- `n = x * k⁻¹` lies both in `N ⊆ (x • K)ᶜ` and in `x • K`, a contradiction.
  exact hN (hnk ▸ hn) (mem_leftCoset x (inv_mem_iff.mpr hk))

end Work.CFT.MaxProP.ContCohomology.Burnside
