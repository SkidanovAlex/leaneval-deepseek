import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.ReconstructField.LevelCandidate
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `levelGalEquiv` is a homeomorphism for the Krull topologies

Let `ψ : Gal(Ω/K₁) ≃* Gal(Ω/K₂)` be a homeomorphic isomorphism of the absolute Galois groups of
two fields, and let `L ⊆ Ω` be a *finite* intermediate field over `K₁`.  The level correspondence
attached to `ψ` is the isomorphism

`NK.ReconstructField.levelGalEquiv ψ hψ L : Gal(Ω/↥L) ≃* Gal(Ω/↥(levelMap ψ L))`

obtained by composing the Galois correspondence at `L`, the isomorphism `ψ` on the fixing
subgroups, and the inverse Galois correspondence at `levelMap ψ L`.

This file proves that this isomorphism is a **homeomorphism** for the Krull topologies.  The
mathematical content is that

* the Galois correspondence `Gal(Ω/L) ≃* Gal(Ω/K)` (`IntermediateField.fixingSubgroupEquiv`) is a
  homeomorphism between the Krull topology on `Gal(Ω/L)` and the subspace topology on the fixing
  subgroup `≤ Gal(Ω/K)` (`isHomeomorph_fixingSubgroupEquiv`),
* transporting a subgroup along a homeomorphism of topological groups is a homeomorphism
  (`isHomeomorph_equivMapOfInjective`), and
* the transport of a subgroup along an *equality* of subgroups is a homeomorphism
  (`isHomeomorph_subgroupCongr`).

Each of these is proved by exhibiting the explicit inverse and checking continuity in both
directions, except the first, where compactness of the fixing subgroup (a closed subgroup of the
compact group `Gal(Ω/K)`) and Hausdorffness of `Gal(Ω/L)` reduce the verification to continuity,
which is a check on the neighbourhood basis of the Krull topology.

## Contents

* `isHomeomorph_symm'`, `isHomeomorph_trans'` — the inverse and the composite of homeomorphic
  `MulEquiv`s;
* `isHomeomorph_equivMapOfInjective`, `isHomeomorph_subgroupCongr` — subgroup transport;
* `isHomeomorph_fixingSubgroupEquiv` — the Galois correspondence;
* `isHomeomorph_levelGalEquiv` — the goal.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace NK.Reconstruct

/-! ### Homeomorphic `MulEquiv`s -/

/-- The inverse of a homeomorphic isomorphism of topological groups is a homeomorphism. -/
theorem isHomeomorph_symm' {G H : Type*} [Group G] [TopologicalSpace G] [Group H]
    [TopologicalSpace H] (e : G ≃* H) (he : IsHomeomorph (e : G → H)) :
    IsHomeomorph ((e.symm : H ≃* G) : H → G) := by
  refine (isHomeomorph_iff_exists_inverse).mpr ⟨?_, ⇑e, ?_, ?_, he.continuous⟩
  · exact (Equiv.continuous_symm_iff e.toEquiv).mpr he.isOpenMap
  · intro y; exact e.apply_symm_apply y
  · intro x; exact e.symm_apply_apply x

/-- The composite of two homeomorphic isomorphisms of topological groups is a homeomorphism. -/
theorem isHomeomorph_trans' {G H J : Type*} [Group G] [TopologicalSpace G] [Group H]
    [TopologicalSpace H] [Group J] [TopologicalSpace J] (e : G ≃* H) (f : H ≃* J)
    (he : IsHomeomorph (e : G → H)) (hf : IsHomeomorph (f : H → J)) :
    IsHomeomorph ((e.trans f : G ≃* J) : G → J) := by
  rw [show ⇑(e.trans f : G ≃* J) = ⇑f ∘ ⇑e from MulEquiv.coe_trans e f]
  exact hf.comp he

/-! ### Transport of subgroups -/

/-- **Transport of a subgroup along a homeomorphism of topological groups.**  If `e : G ≃* H` is a
homeomorphism of topological groups and `S ≤ G`, then the induced isomorphism `↥S ≃* ↥(S.map e)` is
a homeomorphism for the subspace topologies. -/
theorem isHomeomorph_equivMapOfInjective {G H : Type*} [Group G] [TopologicalSpace G] [Group H]
    [TopologicalSpace H] (e : G ≃* H) (he : IsHomeomorph (e : G → H)) (S : Subgroup G) :
    IsHomeomorph (Subgroup.equivMapOfInjective S (e : G →* H) e.injective :
      ↥S → ↥(S.map (e : G →* H))) := by
  set E := Subgroup.equivMapOfInjective S (e : G →* H) e.injective with hE
  change IsHomeomorph (⇑(E : ↥S ≃ ↥(S.map (e : G →* H))))
  rw [Equiv.isHomeomorph_iff]
  constructor
  · have h1 : ⇑(E : ↥S ≃ ↥(S.map (e : G →* H))) =
        fun x : ↥S => (⟨e (x : G), Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩⟩ : ↥(S.map (e : G →* H))) := by
      funext x; exact Subtype.ext rfl
    rw [h1]
    exact Continuous.subtype_mk (he.continuous.comp continuous_subtype_val) _
  · have hsymm : Continuous (⇑e.symm : H → G) :=
      (Equiv.continuous_symm_iff e.toEquiv).mpr he.isOpenMap
    have hkey : ∀ y : ↥(S.map (e : G →* H)), ((E.symm y : ↥S) : G) = e.symm (y : H) := by
      intro y
      apply e.injective
      rw [show e ((E.symm y : ↥S) : G) = ((E (E.symm y) : ↥(S.map (e : G →* H))) : H) from rfl,
          MulEquiv.apply_symm_apply]
      exact (e.apply_symm_apply _).symm
    have h2 : ⇑(E : ↥S ≃ ↥(S.map (e : G →* H))).symm =
        fun y : ↥(S.map (e : G →* H)) =>
          (⟨e.symm (y : H), by rw [← hkey y]; exact (E.symm y).2⟩ : ↥S) := by
      funext y; exact Subtype.ext (hkey y)
    rw [h2]
    exact Continuous.subtype_mk (hsymm.comp continuous_subtype_val) _

/-- **Transport of a subgroup along an equality of subgroups.**  If `H = K` are subgroups of a
topological group `G`, the induced isomorphism `↥H ≃* ↥K` is a homeomorphism for the subspace
topologies. -/
theorem isHomeomorph_subgroupCongr {G : Type*} [Group G] [TopologicalSpace G] {H K : Subgroup G}
    (h : H = K) : IsHomeomorph (MulEquiv.subgroupCongr h : ↥H → ↥K) := by
  change IsHomeomorph (⇑(MulEquiv.subgroupCongr h : ↥H ≃ ↥K))
  rw [Equiv.isHomeomorph_iff]
  constructor
  · have h1 : ⇑(MulEquiv.subgroupCongr h : ↥H ≃ ↥K) =
        fun x : ↥H => (⟨(x : G), h ▸ x.2⟩ : ↥K) := by
      funext x; exact Subtype.ext (MulEquiv.subgroupCongr_apply h x)
    rw [h1]
    exact Continuous.subtype_mk continuous_subtype_val _
  · have h2 : ⇑(MulEquiv.subgroupCongr h : ↥H ≃ ↥K).symm =
        fun y : ↥K => (⟨(y : G), h.symm ▸ y.2⟩ : ↥H) := by
      funext y; exact Subtype.ext (MulEquiv.subgroupCongr_symm_apply h y)
    rw [h2]
    exact Continuous.subtype_mk continuous_subtype_val _

/-! ### The Galois correspondence is a homeomorphism -/

/-- **Continuity of the Galois correspondence.**  For a finite intermediate field `L` of a Galois
extension `Ω/K`, the map `σ ↦ σ` from the fixing subgroup of `L` (with the subspace topology of
`Gal(Ω/K)`) to `Gal(Ω/L)` (with its Krull topology) is continuous: the preimage of the fixing
subgroup of a finite `L`-subextension `E` is the fixing subgroup of `E` viewed over `K`, which is
open in `Gal(Ω/K)` because `E` is finite over `K`. -/
theorem continuous_fixingSubgroupEquiv {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    [IsGalois K Ω] (L : IntermediateField K Ω) [FiniteDimensional K L] :
    Continuous ((IntermediateField.fixingSubgroupEquiv L) : ↥(L.fixingSubgroup) → Gal(Ω/↥L)) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one, Filter.tendsto_def]
  intro U hU
  rw [krullTopology_mem_nhds_one_iff ↥L Ω] at hU
  obtain ⟨E, hEfd, hEU⟩ := hU
  haveI : FiniteDimensional ↥L ↥E := hEfd
  have hfe : FiniteDimensional K ↥(IntermediateField.restrictScalars K E) :=
    FiniteDimensional.trans K ↥L ↥E
  haveI := hfe
  refine Filter.mem_of_superset ?_ (Set.preimage_mono hEU)
  apply IsOpen.mem_nhds ?_ ?_
  · rw [isOpen_induced_iff]
    refine ⟨↑(IntermediateField.restrictScalars K E).fixingSubgroup,
      IntermediateField.fixingSubgroup_isOpen _, ?_⟩
    ext x
    simp only [Set.mem_preimage, SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    exact ⟨fun h y hy => h y hy, fun h y hy => h y (show y ∈ (E : Set Ω) from hy)⟩
  · simp

/-- **The Galois correspondence is a homeomorphism.**  For a finite intermediate field `L` of a
Galois extension `Ω/K`, the isomorphism `Gal(Ω/L) ≃* Gal(Ω/K)` of Mathlib's
`IntermediateField.fixingSubgroupEquiv`, mapping `Gal(Ω/L)` onto the fixing subgroup of `L` with the
subspace topology of `Gal(Ω/K)`, is a homeomorphism for the Krull topologies.

The fixing subgroup of `L` is closed in the compact group `Gal(Ω/K)`
(`InfiniteGalois.fixingSubgroup_isClosed`), hence compact, and `Gal(Ω/L)` is Hausdorff
(`krullTopology_t2`), so `isHomeomorph_iff_continuous_bijective` reduces the claim to continuity. -/
theorem isHomeomorph_fixingSubgroupEquiv {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    [IsGalois K Ω] (L : IntermediateField K Ω) [FiniteDimensional K L] :
    IsHomeomorph ((IntermediateField.fixingSubgroupEquiv L) : ↥(L.fixingSubgroup) → Gal(Ω/↥L)) := by
  haveI : CompactSpace Gal(Ω/K) := inferInstance
  haveI : CompactSpace ↥(L.fixingSubgroup) :=
    isCompact_iff_compactSpace.mp (InfiniteGalois.fixingSubgroup_isClosed L).isCompact
  have hsep : Algebra.IsSeparable K Ω := IsGalois.to_isSeparable
  have halg : Algebra.IsAlgebraic K Ω := hsep.isAlgebraic
  haveI : Algebra.IsAlgebraic ↥L Ω := Algebra.IsAlgebraic.tower_top (K := K) (A := Ω) ↥L
  haveI : Algebra.IsIntegral ↥L Ω := Algebra.IsAlgebraic.isIntegral
  haveI : T2Space Gal(Ω/↥L) := krullTopology_t2
  exact (isHomeomorph_iff_continuous_bijective).mpr
    ⟨continuous_fixingSubgroupEquiv L, (IntermediateField.fixingSubgroupEquiv L).bijective⟩

/-! ### The main result -/

/-- **`levelGalEquiv` is a homeomorphism.**  The level isomorphism induced by a homeomorphic
isomorphism `ψ` of absolute Galois groups is a homeomorphism for the Krull topologies. -/
theorem isHomeomorph_levelGalEquiv {K₁ K₂ : Type*} [Field K₁] [NumberField K₁] [Field K₂]
    [NumberField K₂] {Ω : Type*} [Field Ω] [Algebra K₁ Ω] [Algebra K₂ Ω]
    [IsSepClosure K₁ Ω] [IsSepClosure K₂ Ω] (ψ : Gal(Ω/K₁) ≃* Gal(Ω/K₂))
    (hψ : IsHomeomorph ψ) (L : IntermediateField K₁ Ω) [FiniteDimensional K₁ L] :
    IsHomeomorph (NK.ReconstructField.levelGalEquiv ψ hψ L) := by
  haveI hL₂ : FiniteDimensional K₂ (NK.Reconstruct.levelMap ψ L) :=
    NK.Reconstruct.finiteDimensional_levelMap hψ L
  rw [NK.ReconstructField.levelGalEquiv]
  refine isHomeomorph_trans' _ _ (isHomeomorph_trans' _ _ ?_ ?_) (isHomeomorph_trans' _ _ ?_ ?_)
  · exact isHomeomorph_symm' _ (isHomeomorph_fixingSubgroupEquiv L)
  · exact isHomeomorph_equivMapOfInjective ψ hψ L.fixingSubgroup
  · exact isHomeomorph_subgroupCongr _
  · exact isHomeomorph_fixingSubgroupEquiv (NK.Reconstruct.levelMap ψ L)

end NK.Reconstruct
