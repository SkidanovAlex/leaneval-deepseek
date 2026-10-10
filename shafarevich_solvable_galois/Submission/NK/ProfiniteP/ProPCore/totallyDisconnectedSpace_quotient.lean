import Mathlib.Topology.Algebra.ClopenNhdofOne
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Quotients of profinite groups are totally disconnected

If `G` is a compact Hausdorff totally disconnected topological group and `N ◁ G` is a closed
normal subgroup, then the quotient topological group `G ⧸ N` is again totally disconnected.

The proof does not need any structure theory of profinite groups: we show that `G ⧸ N` is
* totally separated*. Given distinct `x y : G ⧸ N` we produce a clopen set containing `x` but
not `y`. For this it suffices (translating by `x`) to find an *open* subgroup of `G ⧸ N` that
does not contain `x⁻¹ * y ≠ 1`. Such a subgroup is obtained as the image of an open normal
subgroup `M` of `G` chosen so small that `g * M` avoids `N`, where `g ∈ G` lifts `x⁻¹ * y`.
Open subgroups of a topological group are automatically closed, whence clopen.
-/

namespace NK.ProfiniteP.ProPCore

open Topology

/-- In a compact Hausdorff totally disconnected topological group `G`, for every element `d ≠ 1`
of the quotient `G ⧸ N` by a closed normal subgroup there is an open subgroup of `G ⧸ N` not
containing `d`. -/
theorem exists_openSubgroup_quotient_not_mem {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    {N : Subgroup G} [N.Normal] (hN : IsClosed (N : Set G))
    {d : G ⧸ N} (hd : d ≠ 1) :
    ∃ L : Subgroup (G ⧸ N), IsOpen (L : Set (G ⧸ N)) ∧ d ∉ L := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective d
  have hgN : g ∉ N := fun h => hd ((QuotientGroup.eq_one_iff g).mpr h)
  -- a neighbourhood of `1` all of whose elements keep `g` outside `N`
  have hB : IsOpen {x : G | g * x ∉ (N : Set G)} :=
    hN.isOpen_compl.preimage (continuous_const_mul g)
  have h1B : (1 : G) ∈ {x : G | g * x ∉ (N : Set G)} := by simpa using hgN
  obtain ⟨M, hM⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hB h1B
  have hMopen : IsOpen (((M : Subgroup G)) : Set G) := M.isOpen
  refine ⟨Subgroup.map (QuotientGroup.mk' N) (M : Subgroup G), ?_, ?_⟩
  · -- the image of an open subgroup under the (open) quotient map is open
    have hopen : IsOpen ((QuotientGroup.mk' N) '' (((M : Subgroup G)) : Set G)) := by
      simpa [QuotientGroup.mk'_apply] using
        ((QuotientGroup.isOpenMap_coe : IsOpenMap (QuotientGroup.mk : G → G ⧸ N))
          (((M : Subgroup G)) : Set G) hMopen)
    rw [Subgroup.coe_map]
    exact hopen
  · -- `mk g` is not in the image of `M`
    intro hmem
    rw [Subgroup.mem_map] at hmem
    obtain ⟨m, hm, hmk⟩ := hmem
    have hmk' : (QuotientGroup.mk' N) m = (QuotientGroup.mk' N) g := by
      simpa [QuotientGroup.mk'_apply] using hmk
    have hker : (QuotientGroup.mk' N) (m * g⁻¹) = 1 := by
      rw [map_mul, map_inv, hmk', mul_inv_cancel]
    have hmg : m * g⁻¹ ∈ N := by
      rw [← QuotientGroup.ker_mk' N]; exact hker
    have hgm : g * m⁻¹ ∈ N := by
      have := N.inv_mem hmg
      simpa [mul_inv_rev] using this
    exact (hM ((M : Subgroup G).inv_mem hm)) (by simpa using hgm)

/-- The quotient of a compact Hausdorff totally disconnected topological group by a closed normal
subgroup is totally disconnected. -/
theorem totallyDisconnectedSpace_quotient {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [TotallyDisconnectedSpace G]
    {N : Subgroup G} [N.Normal] (hN : IsClosed (N : Set G)) : TotallyDisconnectedSpace (G ⧸ N) := by
  have hTS : TotallySeparatedSpace (G ⧸ N) := by
    refine ⟨fun x _ y _ hxy => ?_⟩
    have hd : x⁻¹ * y ≠ 1 := fun h => hxy (inv_mul_eq_one.mp h)
    obtain ⟨L, hLopen, hLd⟩ := exists_openSubgroup_quotient_not_mem (G := G) (N := N) hN hd
    have hLclosed : IsClosed (L : Set (G ⧸ N)) := L.isClosed_of_isOpen hLopen
    have hu_open : IsOpen {z : G ⧸ N | x⁻¹ * z ∈ L} := hLopen.preimage (continuous_const_mul x⁻¹)
    have hu_closed : IsClosed {z : G ⧸ N | x⁻¹ * z ∈ L} :=
      hLclosed.preimage (continuous_const_mul x⁻¹)
    exact ⟨{z : G ⧸ N | x⁻¹ * z ∈ L}, {z : G ⧸ N | x⁻¹ * z ∈ L}ᶜ, hu_open,
      hu_closed.isOpen_compl, by simp, hLd, by intro z _; simp, disjoint_compl_right⟩
  exact hTS.totallyDisconnectedSpace

end NK.ProfiniteP.ProPCore
