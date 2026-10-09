import Mathlib
import Submission.NK.LocalStructure.Tower.other_bounded_of_towerCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

/-!
# Nikolov–Segal at the base field `κ`: every finite-index subgroup of `Gal(K'/κ)` is closed

`NK.LocalStructure.TowerRankCore K 𝔭 K' p` records the Nikolov–Segal input at the levels
`Gal(K'/↥M)` of the *intermediate fields* `M` of `K'/κ`, together with the level `M = ⊥`
(which is `Gal(K'/↥⊥)`, a group isomorphic — but not equal — to the top group
`Gal(K'/κ) = Gal(K'/𝔭.adicCompletion K)`).

The present file transports that input to the top group itself, which is the form the
consumers use (`NK.LocalStructure.Tower.not_hasUnboundedTowerRank_of_card_extensions_le`
and `NK.LocalStructure.Brauer.exists_intermediateField_of_le_stabilizer` both take a
hypothesis `∀ H : Subgroup Gal(κ'/κ), H.FiniteIndex → IsClosed (H : Set Gal(κ'/κ))`).

The transport is along the canonical isomorphism
`NK.LocalStructure.Tower.botGalEquiv : Gal(K'/κ) ≃* Gal(K'/↥⊥)`, which is the *identity* on the
underlying functions `K' → K'` (`botGalEquiv_apply_coe` is `rfl`).  Since the Krull topology on
`Gal(K'/κ)` has as a neighbourhood basis of `1` the subgroups `Gal(K'/E)` for the *finite*
intermediate fields `E/κ`, and the intermediate fields of `K'/↥⊥` are exactly those of `K'/κ`
(transported by `IntermediateField.restrictScalars`), `botGalEquiv` is also a homeomorphism:
the preimage of a basic neighbourhood `Gal(K'/M)` is the basic neighbourhood of
`M.restrictScalars κ`, whose finiteness over `κ` is
`NK.LocalStructure.Tower.finrank_restrictScalars_bot`.

Only the continuity of `botGalEquiv` (not of its inverse) is needed: a finite-index subgroup
`H ≤ Gal(K'/κ)` is the preimage of the finite-index subgroup `H.map botGalEquiv`, which is
closed by the `TowerRankCore` input at the level `⊥`.
-/

open scoped Topology
open IsDedekindDomain.HeightOneSpectrum

namespace NK.Mine

open NK.LocalStructure.Tower

/-- **The preimage of a basic Krull neighbourhood.**  For an intermediate field
`E` of `K'` over `↥⊥`, the preimage under `botGalEquiv` of the fixing subgroup of `E` (a subgroup
of `Gal(K'/↥⊥)`) is the fixing subgroup of the same subfield `E` viewed over `κ` — the two fixing
subgroups consist of the same automorphisms of `K'`, since `botGalEquiv` is the identity on the
underlying functions. -/
lemma botGalEquiv_preimage_fixingSubgroup {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K']
    (E : IntermediateField ↥(⊥ : IntermediateField κ K') K') :
    (botGalEquiv (κ := κ) (K' := K')) ⁻¹'
        (E.fixingSubgroup : Set Gal(K'/↥(⊥ : IntermediateField κ K')))
      = ((IntermediateField.restrictScalars κ E).fixingSubgroup : Set Gal(K'/κ)) := by
  ext σ
  simp only [Set.mem_preimage, SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  constructor <;> intro h x hx <;> exact h x hx

/-- **`botGalEquiv` is continuous for the Krull topologies.**  The basic neighbourhoods of `1` in
`Gal(K'/↥⊥)` are the fixing subgroups of the finite intermediate fields `E/↥⊥`; the preimage of
`Gal(K'/E)` is `Gal(K'/(E.restrictScalars κ))` (`botGalEquiv_preimage_fixingSubgroup`), which is a
basic neighbourhood because `E` is also finite over `κ`
(`finrank_restrictScalars_bot`).  Continuity at `1` upgrades to continuity because both sides are
topological groups. -/
lemma continuous_botGalEquiv {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K'] [IsGalois κ K'] :
    Continuous (botGalEquiv (κ := κ) (K' := K')) := by
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _)
  intro N hN
  rw [map_one, krullTopology_mem_nhds_one_iff] at hN
  obtain ⟨E, hEfin, hEN⟩ := hN
  have hfin : FiniteDimensional κ ↥(IntermediateField.restrictScalars κ E) := by
    have hfr := finrank_restrictScalars_bot (κ := κ) E
    have hpos : 0 < Module.finrank ↥(⊥ : IntermediateField κ K') ↥E := by
      rw [Module.finrank_pos_iff]
      exact inferInstance
    refine FiniteDimensional.of_finrank_pos ?_
    rw [hfr]
    exact hpos
  haveI := hfin
  have hopen : ((IntermediateField.restrictScalars κ E).fixingSubgroup : Set Gal(K'/κ)) ∈
      𝓝 (1 : Gal(K'/κ)) :=
    (IntermediateField.fixingSubgroup_isOpen (IntermediateField.restrictScalars κ E)).mem_nhds
      (Subgroup.one_mem _)
  refine Filter.mem_of_superset hopen ?_
  rw [← botGalEquiv_preimage_fixingSubgroup E]
  exact Set.preimage_mono hEN

/-- **Nikolov–Segal for `Gal(K'/𝔭.adicCompletion K)` from the reduced tower-rank core.**

`TowerRankCore.finiteIndex_isClosed` gives the statement for the levels `Gal(K'/↥M)`, in particular
for `M = ⊥`.  The canonical identification
`Gal(K'/κ) ≃* Gal(K'/↥⊥)` (`botGalEquiv`) is the identity on the underlying functions and is
continuous (`continuous_botGalEquiv`), so a finite-index subgroup `H ≤ Gal(K'/κ)` is the preimage
of the finite-index subgroup `H.map botGalEquiv ≤ Gal(K'/↥⊥)`, which is closed.

This is the form in which the Nikolov–Segal input is consumed downstream
(`NK.LocalStructure.Tower.not_hasUnboundedTowerRank_of_card_extensions_le`,
`NK.LocalStructure.Brauer.exists_intermediateField_of_le_stabilizer`). -/
theorem finiteIndex_isClosed_of_towerRankCore {K : Type} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ}
    (h : NK.LocalStructure.TowerRankCore K 𝔭 K' p) :
    ∀ H : Subgroup (Gal(K'/𝔭.adicCompletion K)), H.FiniteIndex →
      IsClosed (H : Set (Gal(K'/𝔭.adicCompletion K))) := by
  intro H hH
  haveI : IsGalois (𝔭.adicCompletion K) K' := IsSepClosure.isGalois
  have hidx : (H.map (botGalEquiv (κ := 𝔭.adicCompletion K) (K' := K')).toMonoidHom).index
      = H.index :=
    Subgroup.index_map_equiv H (botGalEquiv (κ := 𝔭.adicCompletion K) (K' := K'))
  have hfin : (H.map (botGalEquiv (κ := 𝔭.adicCompletion K) (K' := K')).toMonoidHom).FiniteIndex :=
    ⟨by rw [hidx]; exact hH.index_ne_zero⟩
  have hcl := h.finiteIndex_isClosed ⊥ _ hfin
  have hsub : (H : Set (Gal(K'/𝔭.adicCompletion K))) =
      (botGalEquiv (κ := 𝔭.adicCompletion K) (K' := K')) ⁻¹'
        ((H.map (botGalEquiv (κ := 𝔭.adicCompletion K) (K' := K')).toMonoidHom :
          Subgroup Gal(K'/↥(⊥ : IntermediateField (𝔭.adicCompletion K) K'))) :
            Set Gal(K'/↥(⊥ : IntermediateField (𝔭.adicCompletion K) K'))) := by
    ext σ
    simp only [Set.mem_preimage, SetLike.mem_coe]
    rw [Subgroup.mem_map_equiv]
    simp
  rw [hsub]
  exact hcl.preimage (continuous_botGalEquiv (κ := 𝔭.adicCompletion K) (K' := K'))

end NK.Mine
