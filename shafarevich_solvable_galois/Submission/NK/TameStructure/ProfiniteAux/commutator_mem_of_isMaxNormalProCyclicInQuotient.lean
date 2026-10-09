import Mathlib
import Submission.NK.LocalTame.Basic
import Submission.NK.LocalTame.Galois
import Submission.NK.LocalStructure.Tame.commute_of_isProCyclic_of_profinite
import Submission.NK.ProfiniteP.ProPCore.totallyDisconnectedSpace_quotient
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace NK.TameStructure.ProfiniteAux

/-- **The commutator relation `[I, I] ≤ V` from the maximality of `I/V`.**

If `I` is the subgroup whose image in `G ⧸ V` is the maximal closed normal pro-cyclic subgroup
(the tame inertia `I_κ` modulo the wild inertia `V_κ`), then the image `I/V` is pro-cyclic, hence
abelian, so the commutator of any two elements of `I` lies in `V`.

The maximality component of the hypothesis is *not* used: pro-cyclicity of `I/V` alone suffices.
What is needed beyond the abstract group theory is the topology: `G` is a compact totally
disconnected topological group and `V` is closed, so that the closed subgroup
`quotientImage V I ≤ G ⧸ V` maps onto a compact totally disconnected topological group, to which
`NK.LocalStructure.Tame.commute_of_isProCyclic_of_profinite` applies. -/
theorem commutator_mem_of_isMaxNormalProCyclicInQuotient {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [CompactSpace G]
    [TotallyDisconnectedSpace G] {V I : Subgroup G} [V.Normal] (hVc : IsClosed (V : Set G))
    (hI : I.Normal) (hIc : IsClosed (I : Set G))
    (h : NK.LocalTame.IsMaxNormalProCyclicInQuotient V I) :
    ∀ y ∈ I, ∀ z ∈ I, y * z * y⁻¹ * z⁻¹ ∈ V := by
  -- the quotient `G ⧸ V` is again compact and totally disconnected
  haveI hTD : TotallyDisconnectedSpace (G ⧸ V) :=
    NK.ProfiniteP.ProPCore.totallyDisconnectedSpace_quotient hVc
  -- `↑I` is compact in `G`, hence its image `quotientImage V I` is compact in `G ⧸ V`
  have hIcomp : IsCompact (I : Set G) := hIc.isCompact
  have hset : (QuotientGroup.mk' V) '' (I : Set G) = QuotientGroup.mk '' (I : Set G) := by
    apply Set.image_congr
    intro x _
    exact QuotientGroup.mk'_apply V x
  have hImcomp : IsCompact
      ((NK.LocalTame.quotientImage V I : Subgroup (G ⧸ V)) : Set (G ⧸ V)) := by
    rw [NK.LocalTame.quotientImage, Subgroup.coe_map, hset]
    exact hIcomp.image (QuotientGroup.continuous_mk (N := V))
  haveI hHcomp : CompactSpace ↥(NK.LocalTame.quotientImage V I) :=
    isCompact_iff_compactSpace.mp hImcomp
  -- `I/V` is pro-cyclic, hence, being a compact totally disconnected topological group, abelian
  have hcomm := NK.LocalStructure.Tame.commute_of_isProCyclic_of_profinite h.2.2.1
  intro y hy z hz
  have hy' : (QuotientGroup.mk' V) y ∈ NK.LocalTame.quotientImage V I := by
    rw [NK.LocalTame.quotientImage]
    exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
  have hz' : (QuotientGroup.mk' V) z ∈ NK.LocalTame.quotientImage V I := by
    rw [NK.LocalTame.quotientImage]
    exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
  -- the images of `y` and `z` commute in `G ⧸ V`
  have hc : (QuotientGroup.mk' V) y * (QuotientGroup.mk' V) z =
      (QuotientGroup.mk' V) z * (QuotientGroup.mk' V) y := by
    have h2 := congrArg Subtype.val
      (hcomm ⟨(QuotientGroup.mk' V) y, hy'⟩ ⟨(QuotientGroup.mk' V) z, hz'⟩)
    simpa using h2
  -- hence the commutator is trivial in `G ⧸ V`, i.e. it lies in `V`
  have h1 : (QuotientGroup.mk' V) (y * z * y⁻¹ * z⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
    group
  have h2 : (↑(y * z * y⁻¹ * z⁻¹) : G ⧸ V) = 1 := by
    rw [← QuotientGroup.mk'_apply]
    exact h1
  exact (QuotientGroup.eq_one_iff (N := V) (y * z * y⁻¹ * z⁻¹)).mp h2

end NK.TameStructure.ProfiniteAux
