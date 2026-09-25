import Mathlib
import Submission.NK.LocalStructure.Brauer.exists_intermediateField_of_le_stabilizer

/-!
# A finite-index subgroup of the absolute Galois group of a field is the Galois group of a
finite extension of degree the index

This file refines `NK.LocalStructure.Brauer.exists_intermediateField_of_finiteIndex` by
computing the *degree* of the fixed field: if `H ≤ K ≤ G` with `K ≃* Gal(κ'/κ)` and `H` of
finite relative index in `K`, then `H ≃* Gal(κ'/N)` for the fixed field `N` of the image of `H`,
and `[N : κ] = [K : H]`.  The degree count is the Galois correspondence in the form
`IntermediateField.finrank_eq_fixingSubgroup_index`
(`[L : κ] = index of the fixing subgroup of L`), valid for any intermediate field of a Galois
extension, together with `Subgroup.index_map_equiv` for the isomorphism `K ≃* Gal(κ'/κ)`.

This is the rank count used in Neukirch's characterisation of decomposition groups
(CoNF (12.1.9)): the degree of the finite extension is exactly the index of the subgroup.
-/

open scoped Classical Pointwise

universe u

namespace NK.LocalDecomposition

/-- **Degree refinement of the Galois correspondence for finite-index subgroups.**  Let
`e : K ≃* Gal(κ'/κ)` be an isomorphism of a subgroup `K ≤ G` with the absolute Galois group of a
separable closure `κ'` of `κ`, and let `H ≤ K` have finite relative index.  If every finite-index
subgroup of `Gal(κ'/κ)` is closed, then there is an intermediate field `N` with
`[N : κ] = H.relIndex K` and `H ≃* Gal(κ'/N)`.

Concretely `N` is the fixed field of `e(H)` under the Galois correspondence: it is finite over `κ`
because `e(H)` is closed of finite index, and its degree over `κ` is the index of its fixing
subgroup, which is `H.relIndex K`. -/
theorem exists_intermediateField_of_finiteIndex_finrank {G κ κ' : Type u} [Group G] [Field κ]
    [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']
    (K : Subgroup G) (e : K ≃* Gal(κ'/κ)) (H : Subgroup G) (hHK : H ≤ K)
    (hrel : 0 < H.relIndex K)
    (hclosed : ∀ U : Subgroup Gal(κ'/κ), U.FiniteIndex → IsClosed (U : Set Gal(κ'/κ))) :
    ∃ N : IntermediateField κ κ', Module.finrank κ ↥N = H.relIndex K ∧
      Nonempty (H ≃* Gal(κ'/↥N)) := by
  classical
  -- `H` as a subgroup of `K`, and its image in `Gal(κ'/κ)`.
  let Ksub : Subgroup K := H.subgroupOf K
  let H' : Subgroup Gal(κ'/κ) := Ksub.map (e : K →* Gal(κ'/κ))
  -- The image of `H` has finite index: `e` is bijective.
  have hH'fin : H'.FiniteIndex := by
    rw [Subgroup.finiteIndex_iff]
    show (Ksub.map (e : K →* Gal(κ'/κ))).index ≠ 0
    rw [Subgroup.index_map_equiv Ksub e]
    exact ne_of_gt hrel
  -- Finite index plus the topological input: the image is closed.
  have hH'closed : IsClosed (H' : Set Gal(κ'/κ)) := hclosed H' hH'fin
  let C : ClosedSubgroup Gal(κ'/κ) := ⟨H', hH'closed⟩
  -- The corresponding intermediate field of `κ'/κ`.
  let N : IntermediateField κ κ' := IntermediateField.fixedField H'
  have hNfix : N.fixingSubgroup = H' := InfiniteGalois.fixingSubgroup_fixedField C
  refine ⟨N, ?_, ?_⟩
  · -- The degree is the index of the fixing subgroup, which is `H.relIndex K`.
    rw [IntermediateField.finrank_eq_fixingSubgroup_index (L := N), hNfix]
    show H'.index = H.relIndex K
    rw [Subgroup.index_map_equiv Ksub e]
    rfl
  · -- `H ≃ Ksub ≃ H' = N.fixingSubgroup ≃ Gal(κ'/N)`.
    refine ⟨(Subgroup.subgroupOfEquivOfLe hHK).symm.trans
      ((Subgroup.equivMapOfInjective Ksub (e : K →* Gal(κ'/κ)) e.injective).trans
        ((MulEquiv.subgroupCongr hNfix).symm.trans (IntermediateField.fixingSubgroupEquiv N)))⟩

end NK.LocalDecomposition
