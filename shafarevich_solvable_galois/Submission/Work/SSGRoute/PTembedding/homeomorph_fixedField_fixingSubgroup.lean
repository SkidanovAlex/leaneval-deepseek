import Mathlib

/-!
# `K.fixingSubgroup ≃* Gal(Ω/↥K)` is a homeomorphism for the Krull topology

For a Galois extension `Ω/k` and an intermediate field `K`, the canonical group isomorphism

`IntermediateField.fixingSubgroupEquiv K : K.fixingSubgroup ≃* Gal(Ω/↥K)`

(which identifies an automorphism of `Ω/k` that fixes `K` with the same automorphism regarded over
`↥K`) is a **homeomorphism** when `K.fixingSubgroup` carries the subspace topology of
`Gal(Ω/k) = Ω ≃ₐ[k] Ω` and `Gal(Ω/↥K)` carries its Krull topology.

In particular no finiteness of `K` over `k` is required: the two topologies agree in general.

## Proof

* The restriction map `Gal(Ω/↥K) →* Gal(Ω/k)`, `σ ↦ σ.restrictScalars k`, is continuous: a basic
  Krull neighbourhood of `1` in `Gal(Ω/k)` is `Gal(Ω/M)` for an intermediate field `M` finite over
  `k`, and its preimage contains `Gal(Ω/K·M)`, where `K·M = adjoin ↥K M` is finite over `K` because
  `M/k` is finite and `Ω/k` is algebraic (`adjoin_rank_le_of_isAlgebraic_right`).
  Since the subspace topology on `K.fixingSubgroup ⊆ Gal(Ω/k)` is the topology induced by
  `Subtype.val`, this also gives the continuity of `(fixingSubgroupEquiv K).symm`.
* The domain `K.fixingSubgroup` is a *closed* subgroup of the *compact* group `Gal(Ω/k)`, hence
  compact, while `Gal(Ω/↥K)` is Hausdorff (`krullTopology_t2`, as `Ω/↥K` is algebraic).  So the
  continuous bijection `⇑(fixingSubgroupEquiv K)` is a homeomorphism
  (`isHomeomorph_iff_continuous_bijective`).

## Application

`D` is a closed subgroup of `Gal(Ω/k)`; its fixed field `K = fixedField D` satisfies
`K.fixingSubgroup = D` (the infinite Galois correspondence), so this file identifies the Krull
topology on `Gal(Ω/K)` with the subspace topology on `D` — the input needed to transfer
(co)homological statements between `Gal(Ω/K)` and `D` (e.g. Hilbert 90 at `D`).
-/

namespace Work.SSGRoute.PTembedding

open scoped IntermediateField Topology
open Filter

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

section Adjoin

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- If `M` is an intermediate field finite-dimensional over `F`, then the compositum of `M` with
an arbitrary intermediate field `K` is finite-dimensional over `↥K`. -/
lemma finiteDimensional_adjoin_restrictScalars (K M : IntermediateField F E)
    [FiniteDimensional F M] :
    FiniteDimensional ↥K (IntermediateField.adjoin ↥K (M : Set E)) := by
  have h := IntermediateField.adjoin_rank_le_of_isAlgebraic_right (E := ↥K) (F := F) (K := E) M
  exact Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt h (Module.rank_lt_aleph0 F ↥M))

end Adjoin

section Continuity

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- The restriction map `Gal(E/↥K) →* Gal(E/F)`, sending `σ` to `σ.restrictScalars F`. -/
noncomputable def restrictGal (K : IntermediateField F E) :
    (E ≃ₐ[↥K] E) →* (E ≃ₐ[F] E) :=
  (Subgroup.subtype K.fixingSubgroup).comp
    ((IntermediateField.fixingSubgroupEquiv K).symm).toMonoidHom

/-- The restriction map `Gal(E/↥K) →* Gal(E/F)` is continuous for the Krull topologies. -/
lemma continuous_restrictGal (K : IntermediateField F E) : Continuous (restrictGal K) := by
  refine continuous_of_continuousAt_one (restrictGal K) ?_
  rw [continuousAt_def, (restrictGal K).map_one]
  intro U hU
  obtain ⟨M, hMfin, hMU⟩ := (krullTopology_mem_nhds_one_iff F E U).mp hU
  haveI : FiniteDimensional F M := hMfin
  let N : IntermediateField ↥K E := IntermediateField.adjoin ↥K (M : Set E)
  haveI : FiniteDimensional ↥K N := finiteDimensional_adjoin_restrictScalars K M
  refine Filter.mem_of_superset
    ((IntermediateField.fixingSubgroup_isOpen N).mem_nhds N.fixingSubgroup.one_mem) ?_
  intro ψ hψ
  show (restrictGal K) ψ ∈ U
  apply hMU
  refine (IntermediateField.mem_fixingSubgroup_iff M ((restrictGal K) ψ)).mpr ?_
  intro x hx
  have hxN : x ∈ N := IntermediateField.subset_adjoin ↥K (M : Set E) hx
  exact (IntermediateField.mem_fixingSubgroup_iff N ψ).mp hψ x hxN

/-- The inverse of `fixingSubgroupEquiv K`, i.e. the restriction map
`Gal(E/↥K) → ↥K.fixingSubgroup`, is continuous for the Krull topologies. -/
lemma continuous_symm_fixingSubgroupEquiv (K : IntermediateField F E) :
    Continuous (⇑((IntermediateField.fixingSubgroupEquiv K).symm) :
      (E ≃ₐ[↥K] E) → ↥K.fixingSubgroup) := by
  have h : Continuous (Subtype.val ∘
      (⇑((IntermediateField.fixingSubgroupEquiv K).symm) : (E ≃ₐ[↥K] E) → ↥K.fixingSubgroup)) :=
    continuous_restrictGal K
  exact (Topology.IsInducing.subtypeVal
    (t := (K.fixingSubgroup : Set (E ≃ₐ[F] E)))).continuous_iff.mpr h

end Continuity

/-- General form: for a Galois extension `E/F` and *any* intermediate field `K`, the canonical
isomorphism `K.fixingSubgroup ≃* Gal(E/↥K)` (with `K.fixingSubgroup` carrying the subspace
topology of `Gal(E/F)` and `Gal(E/↥K)` its Krull topology) is a homeomorphism. -/
theorem isHomeomorph_fixingSubgroupEquiv {F E : Type*} [Field F] [Field E] [Algebra F E]
    [IsGalois F E] (K : IntermediateField F E) :
    IsHomeomorph (⇑(IntermediateField.fixingSubgroupEquiv K) :
      ↥K.fixingSubgroup → (E ≃ₐ[↥K] E)) := by
  -- `E/↥K` is Galois, and `E/F`, `E/↥K` are algebraic
  haveI : IsGalois ↥K E := IsGalois.tower_top_of_isGalois F ↥K E
  haveI : Algebra.IsIntegral F E :=
    Algebra.isAlgebraic_iff_isIntegral.mp (Algebra.IsSeparable.isAlgebraic F E)
  haveI : Algebra.IsIntegral ↥K E :=
    Algebra.isAlgebraic_iff_isIntegral.mp (Algebra.IsSeparable.isAlgebraic ↥K E)
  -- `Gal(E/F)` is compact Hausdorff, so its closed subgroup `K.fixingSubgroup` is compact, and
  -- `Gal(E/↥K)` is Hausdorff.
  haveI : T2Space (E ≃ₐ[F] E) := krullTopology_t2
  haveI : CompactSpace (E ≃ₐ[F] E) := inferInstance
  haveI : T2Space ↥K.fixingSubgroup := inferInstance
  haveI : CompactSpace ↥K.fixingSubgroup := by
    have hclosed : IsClosed (K.fixingSubgroup : Set (E ≃ₐ[F] E)) :=
      InfiniteGalois.fixingSubgroup_isClosed K
    exact isCompact_iff_compactSpace.mp hclosed.isCompact
  haveI : CompactSpace (E ≃ₐ[↥K] E) := inferInstance
  haveI : T2Space (E ≃ₐ[↥K] E) := krullTopology_t2
  -- the inverse (the restriction map) is continuous …
  have hsymm : Continuous (⇑((IntermediateField.fixingSubgroupEquiv K).symm) :
      (E ≃ₐ[↥K] E) → ↥K.fixingSubgroup) := continuous_symm_fixingSubgroupEquiv K
  -- … hence the map itself is continuous, being a bijection from a compact to a Hausdorff space
  have hcont : Continuous (⇑(IntermediateField.fixingSubgroupEquiv K) :
      ↥K.fixingSubgroup → (E ≃ₐ[↥K] E)) := by
    have h := Continuous.continuous_symm_of_equiv_compact_to_t2
      (f := ((IntermediateField.fixingSubgroupEquiv K).symm).toEquiv) hsymm
    simpa using h
  exact (isHomeomorph_iff_continuous_bijective).mpr
    ⟨hcont, (IntermediateField.fixingSubgroupEquiv K).bijective⟩

theorem homeomorph_fixedField_fixingSubgroup {k Ω : Type} [Field k] [Field Ω]
    [Algebra k Ω] [IsGalois k Ω] (D : Subgroup (Ω ≃ₐ[k] Ω))
    (hD : IsClosed (D : Set (Ω ≃ₐ[k] Ω))) :
    IsHomeomorph ((IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField D)) :
      ↥((IntermediateField.fixedField D).fixingSubgroup) →
        (Ω ≃ₐ[↥(IntermediateField.fixedField D)] Ω)) :=
  isHomeomorph_fixingSubgroupEquiv (IntermediateField.fixedField D)

end Work.SSGRoute.PTembedding
