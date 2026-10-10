import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.NK.LocalStructure.Tower.not_hasUnboundedTowerRank_of_card_extensions_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalStructure.Tower

open scoped Classical Pointwise
open IsDedekindDomain.HeightOneSpectrum

/-! ## Transporting the tower-rank data from the top group to the bottom-field level

`NK.LocalStructure.TowerRankCore.finiteIndex_isClosed` — the Nikolov–Segal input — is stated at
the Galois groups `Gal(K'/↥M)` over the *intermediate fields* `M` of `K'/κ`, i.e. for the
subgroups `M.fixingSubgroup ≤ Gal(K'/κ)`, together with the case `M = ⊥`, where
`Gal(K'/↥⊥) ≅ Gal(K'/κ)` is the top group itself, presented with the base field `↥⊥` rather than
`κ`.  `Gal(K'/↥⊥)` and `Gal(K'/κ)` are different types (the algebra structure on `K'` differs), so
the transfer is recorded here: the canonical isomorphism `botGalEquiv` is the identity on the
underlying functions `K' → K'`, hence induces the identity on the Galois-theoretic data, and only
its algebraic part is needed.

With that, `not_hasUnboundedTowerRank_of_card_extensions_le` can be applied at the base field
`↥⊥` (where the Nikolov–Segal input is available verbatim), and its conclusion transported back. -/

/-- **The canonical isomorphism `Gal(K'/κ) ≃* Gal(K'/↥⊥)`.**

An automorphism of `K'` over `κ` fixes `⊥` pointwise (the bottom intermediate field is the closure
of the image of `κ`), so it is an automorphism over `↥⊥`; conversely the restriction of scalars
along `κ → ↥⊥ → K'` exhibits an automorphism over `↥⊥` as one over `κ`.  Concretely the isomorphism
is `Gal(K'/κ) ≅ ↥⊤ ≅ ↥(⊥.fixingSubgroup) ≅ Gal(K'/↥⊥)`. -/
noncomputable def botGalEquiv {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K'] :
    Gal(K'/κ) ≃* Gal(K'/↥(⊥ : IntermediateField κ K')) :=
  (Subgroup.topEquiv.symm.trans
      (MulEquiv.subgroupCongr
        (IntermediateField.fixingSubgroup_bot (F := κ) (E := K')).symm)).trans
    (IntermediateField.fixingSubgroupEquiv (⊥ : IntermediateField κ K'))

@[simp]
lemma botGalEquiv_apply_coe {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K']
    (σ : Gal(K'/κ)) :
    ((botGalEquiv σ : Gal(K'/↥(⊥ : IntermediateField κ K'))) : K' → K') = σ := rfl

@[simp]
lemma botGalEquiv_symm_apply_coe {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K']
    (σ : Gal(K'/↥(⊥ : IntermediateField κ K'))) :
    ((botGalEquiv.symm σ : Gal(K'/κ)) : K' → K') = σ := rfl

/-- **The fixing subgroups correspond.**  For an intermediate field `M` of `K'` over `↥⊥`, the
fixing subgroup of `M` inside `Gal(K'/↥⊥)` is the image under `botGalEquiv.symm` of the fixing
subgroup of the same subfield viewed over `κ` (the two subfields have the same underlying set of
elements of `K'`, and `botGalEquiv.symm` preserves the underlying functions). -/
lemma map_fixingSubgroup_botGalEquiv_symm {κ K' : Type*} [Field κ] [Field K']
    [Algebra κ K'] (M : IntermediateField ↥(⊥ : IntermediateField κ K') K') :
    (M.fixingSubgroup).map (botGalEquiv.symm.toMonoidHom)
      = (M.restrictScalars κ).fixingSubgroup := by
  ext σ
  simp only [Subgroup.mem_map, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · rintro ⟨τ, hτ, rfl⟩ x hx
    exact hτ x hx
  · intro h
    exact ⟨botGalEquiv σ, fun x hx => h x hx, rfl⟩

/-- **The degree of `M` over `κ` and over `↥⊥` agree.**  For an intermediate field `M` of `K'`
over `↥⊥`, the degree over `↥⊥` equals the degree over `κ` of the same subfield viewed over `κ`.
Both are the index of the fixing subgroup (`finrank_eq_fixingSubgroup_index`) in the corresponding
absolute Galois group, and those two subgroups correspond under the isomorphism `botGalEquiv`. -/
lemma finrank_restrictScalars_bot {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K']
    [IsGalois κ K'] (M : IntermediateField ↥(⊥ : IntermediateField κ K') K') :
    Module.finrank κ (M.restrictScalars κ) = Module.finrank ↥(⊥ : IntermediateField κ K') M := by
  have hmap := map_fixingSubgroup_botGalEquiv_symm (κ := κ) M
  rw [IntermediateField.finrank_eq_fixingSubgroup_index (F := κ) (E' := K')
        (M.restrictScalars κ), ← hmap]
  have hidx : (Subgroup.map (botGalEquiv.symm.toMonoidHom) M.fixingSubgroup).index
      = M.fixingSubgroup.index := Subgroup.index_map_equiv M.fixingSubgroup botGalEquiv.symm
  rw [hidx, ← IntermediateField.finrank_eq_fixingSubgroup_index
    (F := ↥(⊥ : IntermediateField κ K')) (E' := K') M]

theorem other_bounded_of_towerCore {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ}
    (h : NK.LocalStructure.TowerRankCore K 𝔭 K' p) :
    ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      ¬ NK.LocalAnabelian.HasUnboundedTowerRank ℓ (Gal(K'/𝔭.adicCompletion K)) := by
  intro ℓ hℓ hℓp
  obtain ⟨B, hB⟩ := h.card_extensions_le ℓ hℓ hℓp
  -- the `ℓ`-tower rank is bounded at the level of the bottom field `↥⊥`
  have hbot : ¬ NK.LocalAnabelian.HasUnboundedTowerRank ℓ
      (Gal(K'/↥(⊥ : IntermediateField (𝔭.adicCompletion K) K'))) :=
    not_hasUnboundedTowerRank_of_card_extensions_le (κ := ↥(⊥ : IntermediateField
        (𝔭.adicCompletion K) K')) (K' := K') hℓ
      (fun H hH => h.finiteIndex_isClosed ⊥ H hH)
      (fun M H hH => by
        have hfin : H.FiniteIndex :=
          Subgroup.finiteIndex_iff.mpr (by rw [hH]; exact hℓ.ne_zero)
        exact h.finiteIndex_isClosed (M.restrictScalars (𝔭.adicCompletion K)) H hfin)
      ⟨B, fun M e hM =>
        hB (M.restrictScalars (𝔭.adicCompletion K)) e
          (by rw [finrank_restrictScalars_bot]; exact hM)⟩
  intro hunb
  exact hbot (NK.LocalAnabelian.hasUnboundedTowerRank_congr botGalEquiv hunb)

end NK.LocalStructure.Tower
