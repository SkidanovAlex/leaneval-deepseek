import Mathlib
import Submission.NK.LocalStructure.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalStructure.Tower

/-! ## Index-`ℓ` subgroups and degree-`ℓ` intermediate fields

This file proves the key reduction behind `not_hasUnboundedTowerRank_of_card_extensions_le`:
for a Galois extension `K/k` all of whose index-`ℓ` subgroups are closed, the number of
index-`ℓ` subgroups of `Gal(K/k)` equals the number of intermediate fields `L` with
`[L : k] = ℓ`.

The two ingredients are Mathlib's infinite Galois correspondence
(`InfiniteGalois.fixedField_fixingSubgroup`, `InfiniteGalois.fixingSubgroup_fixedField`)
and the degree-index formula (`IntermediateField.finrank_eq_fixingSubgroup_index`).
The closedness hypothesis is what makes the correspondence *bijective on the nose*: for an
arbitrary Galois extension only the **closed** index-`ℓ` subgroups are recovered as
`Gal(K/L)`, so without it the count of index-`ℓ` subgroups could strictly exceed the count
of degree-`ℓ` subfields. -/

/-- **Index-`ℓ` subgroups of a Galois group are degree-`ℓ` intermediate fields.**

For a Galois extension `K/k` in which every index-`ℓ` subgroup is closed, the Galois
correspondence restricts to a bijection between intermediate fields `L` with `[L : k] = ℓ`
and subgroups of `Gal(K/k)` of index `ℓ`. -/
theorem numIndexSubgroups_eq_card_intermediateField {k K : Type*} [Field k] [Field K]
    [Algebra k K] [IsGalois k K] {ℓ : ℕ}
    (hclosed : ∀ H : Subgroup Gal(K/k), H.index = ℓ → IsClosed (H : Set Gal(K/k))) :
    NK.LocalAnabelian.numIndexSubgroups ℓ (Gal(K/k)) =
      Nat.card {L : IntermediateField k K // Module.finrank k L = ℓ} := by
  rw [NK.LocalAnabelian.numIndexSubgroups]
  refine Nat.card_congr ?_
  refine
    { toFun := fun H => ⟨IntermediateField.fixedField H.1, ?_⟩
      invFun := fun L => ⟨L.1.fixingSubgroup, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · -- `fixedField H` has degree `ℓ` because `H` is closed of index `ℓ`
    have h1 := IntermediateField.finrank_eq_fixingSubgroup_index (F := k) (E' := K)
      (IntermediateField.fixedField H.1)
    have h2 := InfiniteGalois.fixingSubgroup_fixedField
      (⟨H.1, hclosed H.1 H.2⟩ : ClosedSubgroup Gal(K/k))
    exact h1.trans ((congrArg Subgroup.index h2).trans H.2)
  · -- the fixing subgroup of a degree-`ℓ` field has index `ℓ`
    have h1 := IntermediateField.finrank_eq_fixingSubgroup_index (F := k) (E' := K)
      (L.1 : IntermediateField k K)
    exact h1.symm.trans L.2
  · intro H
    exact Subtype.ext (InfiniteGalois.fixingSubgroup_fixedField ⟨H.1, hclosed H.1 H.2⟩)
  · intro L
    exact Subtype.ext (InfiniteGalois.fixedField_fixingSubgroup L.1)

/-- **The `ℓ`-tower rank is bounded when the number of degree-`ℓ` extensions of the
finite `ℓ`-power extensions is bounded.**

`HasUnboundedTowerRank ℓ Gal(K'/κ)` demands index-`ℓ` subgroups of *finite index*
subgroups `V ≤ Gal(K'/κ)` whose index is a power of `ℓ`, in unbounded number.  Such a `V`
is closed (`hclosed_all`, e.g. Nikolov–Segal), so it is the fixing subgroup of its fixed
field `M`; the closedness hypothesis `hclosed` on index-`ℓ` subgroups then identifies the
index-`ℓ` subgroups of `V ≅ Gal(K'/M)` with the degree-`ℓ` intermediate fields over `M`,
whose number is bounded by `hbound`. -/
theorem not_hasUnboundedTowerRank_of_card_extensions_le {κ K' : Type*}
    [Field κ] [Field K'] [Algebra κ K'] [IsGalois κ K'] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hclosed_all : ∀ H : Subgroup Gal(K'/κ), H.FiniteIndex → IsClosed (H : Set Gal(K'/κ)))
    (hclosed : ∀ (M : IntermediateField κ K'), ∀ H : Subgroup Gal(K'/↥M), H.index = ℓ →
      IsClosed (H : Set Gal(K'/↥M)))
    (hbound : ∃ B : ℕ, ∀ (M : IntermediateField κ K') (e : ℕ),
      Module.finrank κ M = ℓ ^ e →
      Nat.card {L : IntermediateField ↥M K' // Module.finrank ↥M L = ℓ} ≤ B) :
    ¬ NK.LocalAnabelian.HasUnboundedTowerRank ℓ (Gal(K'/κ)) := by
  intro hhas
  obtain ⟨B, hB⟩ := hbound
  obtain ⟨V, hVfin, ⟨k, hVk⟩, hVlt⟩ := hhas B
  -- `V` is closed, hence the fixing subgroup of its fixed field `M`
  set M : IntermediateField κ K' := IntermediateField.fixedField V with hM
  have hVcl : IsClosed (V : Set Gal(K'/κ)) := hclosed_all V hVfin
  have hMV : M.fixingSubgroup = V := by
    rw [hM]
    exact InfiniteGalois.fixingSubgroup_fixedField ⟨V, hVcl⟩
  -- and `[M : κ] = V.index = ℓ ^ k`
  have hfr : Module.finrank κ M = ℓ ^ k := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index (F := κ) (E' := K') M, hMV, hVk]
  -- the index-`ℓ` subgroups of `V` are the degree-`ℓ` extensions of `M`
  have hcard := numIndexSubgroups_eq_card_intermediateField (k := ↥M) (K := K') (ℓ := ℓ)
    (hclosed M)
  have hnum : NK.LocalAnabelian.numIndexSubgroups ℓ V ≤ B := by
    rw [NK.LocalAnabelian.numIndexSubgroups_congr (MulEquiv.subgroupCongr hMV.symm) ℓ,
        NK.LocalAnabelian.numIndexSubgroups_congr (IntermediateField.fixingSubgroupEquiv M) ℓ,
        hcard]
    exact hB M k hfr
  exact absurd hnum (not_le.mpr hVlt)

end NK.LocalStructure.Tower
