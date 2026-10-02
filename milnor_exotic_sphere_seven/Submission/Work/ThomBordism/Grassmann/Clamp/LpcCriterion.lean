import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

/-!
# A criterion for local path connectedness

If every point of a Hausdorff space `Y` lies in the interior of the image of a continuous map
`K → Y` with `K` compact and locally path connected, then `Y` is locally path connected.

This is the topological engine behind the proof that real algebraic sets are locally path
connected: it reduces the problem to *covering* the germ of the zero locus by finitely many
continuous images of compact locally path connected spaces.
-/

namespace Work.ThomBordism.Grassmann.Clamp

universe u

open Set Topology Filter

/-- A continuous surjection from a compact space onto a Hausdorff space is a quotient map. -/
theorem isQuotientMap_of_compact_t2 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space Y] {f : X → Y} (hf : Continuous f)
    (hsurj : Function.Surjective f) : Topology.IsQuotientMap f := by
  refine ⟨⟨?_⟩, hsurj⟩
  rw [TopologicalSpace.ext_iff]
  intro s
  constructor
  · intro hs
    rw [isOpen_coinduced]
    exact hs.preimage hf
  · intro hs
    rw [isOpen_coinduced] at hs
    have hcm : IsClosedMap f := hf.isClosedMap
    have hclosed_image : IsClosed (f '' (f ⁻¹' s)ᶜ) := hcm _ (isClosed_compl_iff.mpr hs)
    have hset : f '' (f ⁻¹' s)ᶜ = sᶜ := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa using hx
      · intro hy
        obtain ⟨x, rfl⟩ := hsurj y
        exact ⟨x, by simpa using hy, rfl⟩
    have h1 : IsClosed sᶜ := hset ▸ hclosed_image
    exact isClosed_compl_iff.mp h1

/-- **Criterion for local path connectedness.** If every point `y` of a Hausdorff space `Y` lies in
the interior of the image of a continuous map into `Y` from a compact locally path connected space,
then `Y` is locally path connected. -/
theorem locallyPathConnectedSpace_of_forall_compact_image {Y : Type u} [TopologicalSpace Y]
    [T2Space Y]
    (h : ∀ y : Y, ∃ (K : Type u) (_ : TopologicalSpace K) (_ : CompactSpace K)
      (_ : LocallyPathConnectedSpace K) (f : K → Y), Continuous f ∧ y ∈ interior (range f)) :
    LocallyPathConnectedSpace Y := by
  rw [locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds]
  intro y u hu hyu
  obtain ⟨K, tK, cK, lK, f, hf, hyint⟩ := h y
  letI : TopologicalSpace K := tK
  haveI : CompactSpace K := cK
  haveI : LocallyPathConnectedSpace K := lK
  set g : K → ↥(range f) := fun k => ⟨f k, mem_range_self k⟩ with hg
  have hgc : Continuous g := hf.subtype_mk _
  have hgs : Function.Surjective g := fun z => by
    obtain ⟨k, hk⟩ := z.2
    exact ⟨k, Subtype.ext hk⟩
  haveI : LocallyPathConnectedSpace ↥(range f) :=
    (isQuotientMap_of_compact_t2 hgc hgs).locallyPathConnectedSpace
  have hmemY : range f ∈ 𝓝 y :=
    mem_of_superset (isOpen_interior.mem_nhds hyint) interior_subset
  have hyrange : y ∈ range f := interior_subset hyint
  have hy' : (⟨y, hyrange⟩ : ↥(range f)) ∈ (Subtype.val ⁻¹' u : Set ↥(range f)) := hyu
  have huo : IsOpen (Subtype.val ⁻¹' u : Set ↥(range f)) := hu.preimage continuous_subtype_val
  obtain ⟨S, ⟨hSnhds, hSpc⟩, hSu⟩ :=
    (LocallyPathConnectedSpace.path_connected_basis (⟨y, hyrange⟩ : ↥(range f))).mem_iff.mp
      (huo.mem_nhds hy')
  have hyS : (⟨y, hyrange⟩ : ↥(range f)) ∈ S := mem_of_mem_nhds hSnhds
  have hmemS : Subtype.val '' S ∈ 𝓝 y := by
    obtain ⟨W, hWS, hWopen, hyW⟩ := mem_nhds_iff.mp hSnhds
    obtain ⟨O, hOopen, hOW⟩ := isOpen_induced_iff.mp hWopen
    refine mem_of_superset (Filter.inter_mem (hOopen.mem_nhds ?_) hmemY) ?_
    · have : (⟨y, hyrange⟩ : ↥(range f)) ∈ Subtype.val ⁻¹' O := by rw [hOW]; exact hyW
      exact this
    · intro z hz
      rw [mem_inter_iff] at hz
      have hmemb : (⟨z, hz.2⟩ : ↥(range f)) ∈ W := by rw [← hOW]; exact hz.1
      exact ⟨⟨z, hz.2⟩, hWS hmemb, rfl⟩
  have hpc : IsPathConnected (Subtype.val '' S) := hSpc.image continuous_subtype_val
  have hsub : Subtype.val '' S ⊆ u := by
    rintro z ⟨s, hs, rfl⟩
    exact hSu hs
  have hyim : y ∈ Subtype.val '' S := ⟨⟨y, hyrange⟩, hyS, rfl⟩
  exact mem_of_superset hmemS (hpc.subset_pathComponentIn hyim hsub)


/-- The image of a compact locally path connected space under a continuous map into a Hausdorff
space is locally path connected. -/
theorem LocallyPathConnectedSpace.of_compact_image {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] [CompactSpace X] [LocallyPathConnectedSpace X]
    {f : X → Y} (hf : Continuous f) : LocallyPathConnectedSpace ↥(range f) := by
  have hgc : Continuous fun x : X => (⟨f x, mem_range_self x⟩ : ↥(range f)) := hf.subtype_mk _
  have hgs : Function.Surjective fun x : X => (⟨f x, mem_range_self x⟩ : ↥(range f)) :=
    fun z => by obtain ⟨x, hx⟩ := z.2; exact ⟨x, Subtype.ext hx⟩
  exact (isQuotientMap_of_compact_t2 hgc hgs).locallyPathConnectedSpace

/-- **Criterion, set form.** If every point of a Hausdorff space `Y` lies in the interior of a
compact locally path connected subset of `Y`, then `Y` is locally path connected. -/
theorem locallyPathConnectedSpace_of_forall_compact_set {Y : Type u} [TopologicalSpace Y]
    [T2Space Y]
    (h : ∀ y : Y, ∃ K : Set Y, IsCompact K ∧ LocallyPathConnectedSpace ↥K ∧ y ∈ interior K) :
    LocallyPathConnectedSpace Y := by
  refine locallyPathConnectedSpace_of_forall_compact_image fun y => ?_
  obtain ⟨K, hKc, hKl, hy⟩ := h y
  exact ⟨↥K, inferInstance, isCompact_iff_compactSpace.mp hKc, hKl, Subtype.val,
    continuous_subtype_val, by simpa using hy⟩

end Work.ThomBordism.Grassmann.Clamp
