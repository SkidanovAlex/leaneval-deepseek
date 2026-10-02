import Mathlib
import Submission.Work.Thom.DiscSphereTopology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# The disc bundle of a Euclidean bundle over a compact base is compact

This is the topological input of the Pontryagin–Thom collapse: for a Euclidean real bundle `Z` over a
**compact** base, the closed unit disc bundle `D(Z) = {p | fibreNorm Z p ≤ 1}` is compact
(`Work.Tubular.isCompact_closedDiscSet`), hence so is the type `DiscSub Z`.

The proof is the standard one: a finite subcover of the base by trivialising open sets, shrunk to a
finite *closed* cover (the shrinking lemma `exists_subset_iUnion_closed_subset`, available in Mathlib
because a compact Hausdorff space is normal); over each piece of the closed cover the disc bundle is
the image of `K_i × closedBall 0 1` under the (continuous) trivialisation inverse, hence compact.
`IsEuclidean` is used exactly to identify `fibreNorm ≤ 1` with the trivialised coordinate being in
the closed unit ball (`Work.Thom.mem_closedDiscSet_iff`).
-/

open scoped Topology
open Set Bundle

open Work.TangentClasses

open Work.Thom

namespace Work.Tubular

noncomputable section

variable {B : Type*} [TopologicalSpace B] [CompactSpace B] [T2Space B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {ι : Type*}

/-- **The closed unit disc bundle of a Euclidean real bundle over a compact base is compact.** -/
theorem isCompact_closedDiscSet (Z : RealBundle B F ι) (hZ : IsEuclidean Z) :
    IsCompact (closedDiscSet Z) := by
  obtain ⟨s, hs⟩ := (isCompact_univ (X := B)).elim_finite_subcover Z.baseSet
    (fun i => Z.isOpen_baseSet i)
    (fun x _ => mem_iUnion.mpr ⟨Z.indexAt x, Z.mem_baseSet_at x⟩)
  have huo : ∀ i : {i // i ∈ s}, IsOpen (Z.baseSet i.1) := fun i => Z.isOpen_baseSet i.1
  have hus : (Set.univ : Set B) ⊆ ⋃ i : {i // i ∈ s}, Z.baseSet i.1 := by
    intro x hx
    obtain ⟨i, his, hxi⟩ := mem_iUnion₂.mp (hs (mem_univ x))
    exact mem_iUnion.mpr ⟨⟨i, his⟩, hxi⟩
  have huf : ∀ x ∈ (Set.univ : Set B), {i : {i // i ∈ s} | x ∈ Z.baseSet i.1}.Finite :=
    fun x _ => Set.toFinite _
  obtain ⟨v, hvuniv, hvclosed, hvsub⟩ :=
    exists_subset_iUnion_closed_subset isClosed_univ huo huf hus
  have hcover : closedDiscSet Z = ⋃ i : {i // i ∈ s},
      (Z.localTriv i.1).invFun '' (v i ×ˢ Metric.closedBall (0 : F) 1) := by
    ext p
    constructor
    · intro hp
      obtain ⟨i, hpi⟩ := mem_iUnion.mp (hvuniv (mem_univ p.1))
      have hsrc : p.1 ∈ Z.baseSet i.1 := hvsub i hpi
      have hmem : p ∈ (Z.localTriv i.1).source := by
        rw [VectorBundleCore.mem_localTriv_source]; exact hsrc
      refine mem_iUnion.mpr ⟨i, (Z.localTriv i.1) p, ⟨hpi, ?_⟩, ?_⟩
      · rw [mem_closedDiscSet_iff hZ i.1 p hsrc] at hp
        simpa [Metric.mem_closedBall] using hp
      · exact (Z.localTriv i.1).symm_apply_apply hmem
    · rw [mem_iUnion]
      rintro ⟨i, q, hq0, hqp⟩
      rw [← hqp]
      obtain ⟨hq1, hq2⟩ := hq0
      have hq : q ∈ (Z.localTriv i.1).target := by
        rw [(Z.localTriv i.1).target_eq]
        exact ⟨hvsub i hq1, mem_univ _⟩
      have hsrc : ((Z.localTriv i.1).invFun q).proj ∈ Z.baseSet i.1 :=
        (VectorBundleCore.mem_localTriv_source Z i.1 ((Z.localTriv i.1).invFun q)).1
          ((Z.localTriv i.1).map_target hq)
      rw [mem_closedDiscSet_iff hZ i.1 _ hsrc]
      have hq' : (Z.localTriv i.1) ((Z.localTriv i.1).invFun q) = q :=
        (Z.localTriv i.1).apply_symm_apply hq
      rw [hq']
      simpa [Metric.mem_closedBall] using hq2
  rw [hcover]
  refine isCompact_iUnion (fun i => ?_)
  refine IsCompact.image_of_continuousOn ?_ ?_
  · exact (IsCompact.of_isClosed_subset isCompact_univ (hvclosed i) (subset_univ _)).prod
      (isCompact_closedBall (0 : F) 1)
  · refine (Z.localTriv i.1).continuousOn_invFun.mono ?_
    rw [(Z.localTriv i.1).target_eq]
    exact Set.prod_mono (hvsub i) (subset_univ _)

/-- **The type of points of the closed unit disc bundle is compact**, for a Euclidean real bundle
over a compact base.  This is the form in which the compactness is used by the collapse map. -/
theorem compactSpace_discSub (Z : RealBundle B F ι) (hZ : IsEuclidean Z) :
    CompactSpace (DiscSub Z) :=
  isCompact_iff_compactSpace.mp (isCompact_closedDiscSet Z hZ)

end

end Work.Tubular
