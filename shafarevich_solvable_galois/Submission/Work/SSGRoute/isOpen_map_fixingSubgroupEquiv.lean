import Mathlib

open scoped IntermediateField Topology

namespace Work.SSGRoute

/-- The group isomorphism `K.fixingSubgroup ≃* Gal(E/↥K)` is compatible with the Krull
topologies: it maps open subgroups of `Gal(E/↥K)` (with the subspace topology inherited from
`Gal(E/F)`) to open subgroups.

Concretely, an open subset `U` of `Gal(E/F)` cutting out `H` restricts to `H`, and the Krull
neighbourhood basis of the identity in `Gal(E/F)` consists of the fixing subgroups of the
finite subextensions `M/F`. The image of `Gal(E/(K⊔M))` under the isomorphism is the fixing
subgroup of `K⊔M` viewed as a finite extension of `K`, which is a basic open subgroup of
`Gal(E/↥K)`. -/
theorem isOpen_map_fixingSubgroupEquiv
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (K : IntermediateField F E) (H : Subgroup ↥K.fixingSubgroup)
    (hH : IsOpen (H : Set ↥K.fixingSubgroup)) :
    IsOpen ((H.map (IntermediateField.fixingSubgroupEquiv K).toMonoidHom : Subgroup Gal(E/↥K)) :
      Set Gal(E/↥K)) := by
  let e := IntermediateField.fixingSubgroupEquiv K
  -- `H` open in the subspace topology means it is the trace of an open set `U ≤ Gal(E/F)`.
  obtain ⟨U, hUopen, hUeq⟩ := isOpen_induced_iff.mp hH
  have h1U : (1 : Gal(E/F)) ∈ U := by
    have : (1 : ↥K.fixingSubgroup) ∈ Subtype.val ⁻¹' U := by
      rw [hUeq]; exact H.one_mem
    simpa using this
  have hUnhds : U ∈ 𝓝 (1 : Gal(E/F)) := hUopen.mem_nhds h1U
  -- `U` contains a basic Krull neighbourhood `Gal(E/M)` with `M/F` finite.
  obtain ⟨M, hMfin, hMsub⟩ := (krullTopology_mem_nhds_one_iff F E U).mp hUnhds
  have key : ∀ h : ↥K.fixingSubgroup, (h : Gal(E/F)) ∈ M.fixingSubgroup → h ∈ H := by
    intro h hh
    have h2 : h ∈ Subtype.val ⁻¹' U := hMsub hh
    rwa [hUeq] at h2
  -- `K⊔M` is finite over `K`; realise it as an `IntermediateField ↥K E`.
  let N : IntermediateField ↥K E := IntermediateField.adjoin ↥K (M : Set E)
  have hNfin : FiniteDimensional ↥K N := by
    have hle := IntermediateField.adjoin_rank_le_of_isAlgebraic_right (F := F) (E := ↥K) (K := E) M
    have hfin : Module.rank F ↥M < Cardinal.aleph0 := Module.rank_lt_aleph0 F ↥M
    have : Module.rank ↥K ↥N < Cardinal.aleph0 := lt_of_le_of_lt hle hfin
    exact Module.rank_lt_aleph0_iff.mp this
  -- It remains to see that `Gal(E/N)` is a neighbourhood of `1` contained in `e '' H`.
  refine Subgroup.isOpen_of_mem_nhds (H.map e.toMonoidHom) (g := 1) ?_
  rw [krullTopology_mem_nhds_one_iff ↥K E (↑(H.map e.toMonoidHom))]
  refine ⟨N, hNfin, ?_⟩
  intro τ hτ
  change τ ∈ N.fixingSubgroup at hτ
  change τ ∈ Subgroup.map e.toMonoidHom H
  rw [Subgroup.mem_map]
  rw [IntermediateField.mem_fixingSubgroup_iff] at hτ
  refine ⟨e.symm τ, ?_, ?_⟩
  · -- `e.symm τ` fixes `M` pointwise, so it lies in `H`.
    apply key
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hxN : x ∈ N := IntermediateField.subset_adjoin ↥K (M : Set E) hx
    have hcoe : (((e.symm τ : ↥K.fixingSubgroup) : Gal(E/F))) x = τ x := by
      rw [← MulEquiv.apply_symm_apply e τ]
      rfl
    rw [hcoe]
    exact hτ x hxN
  · exact e.apply_symm_apply τ

end Work.SSGRoute
