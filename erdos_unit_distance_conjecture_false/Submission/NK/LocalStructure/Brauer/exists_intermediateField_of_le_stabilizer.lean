import Mathlib
import Submission.NK.LocalStructure.Defs
import Submission.NK.NeukirchUchida.nonempty_mulEquiv_decompositionGroupOf_localGalois

/-!
# A finite-index subgroup of a decomposition group is the absolute Galois group of a finite
extension of the local field

This file contains the group-theoretic core of the "localisation" step of Neukirch's
characterisation of decomposition subgroups (CoNF (12.1.9)): if `H` is a subgroup of a group `G`
which is contained, with finite relative index, in a subgroup `K ≤ G` that is isomorphic to the
absolute Galois group `Gal(κ̄/κ)` of a local field `κ`, and if every finite-index subgroup of
`Gal(κ̄/κ)` is closed, then `H` is isomorphic to `Gal(κ̄/N)` for a *finite* extension `N/κ`.

The topological input (`hclosed`) is what the Galois correspondence needs: a finite-index
subgroup of `Gal(κ̄/κ)` is closed, hence the fixed field of its image under the isomorphism is a
finite extension of `κ`.  For `κ = K_𝔭` a `p`-adic field this is supplied by
Nikolov–Segal (`Gal(κ̄/κ)` is topologically finitely generated, so finite-index subgroups are
open); it is the hypothesis `hclosed_local` of the main theorem below.

The number-theoretic input is `NK.NeukirchUchida.nonempty_mulEquiv_decompositionGroupOf_localGalois`:
the decomposition group of a place `A` of a separable closure `K'` of a number field `K` above a
finite prime `𝔭` is the absolute Galois group of the completion `K_𝔭`.
-/

set_option linter.style.haveILetI false

namespace NK.LocalStructure.Brauer

open scoped Classical Pointwise
open IsDedekindDomain.HeightOneSpectrum

universe u

/-- **Group-theoretic core.**  Let `K ≤ G` and let `e : K ≃* Gal(κ'/κ)` be an isomorphism of `K`
with the absolute Galois group of a separable closure `κ'` of `κ`.  If `H ≤ K` has finite relative
index in `K` and every finite-index subgroup of `Gal(κ'/κ)` is closed, then `H` is isomorphic to
`Gal(κ'/N)` for some finite extension `N/κ`.

Concretely, `N` is the fixed field of the image of `H` under `e`. -/
theorem exists_intermediateField_of_finiteIndex
    {G κ κ' : Type u} [Group G] [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']
    (K : Subgroup G) (e : K ≃* Gal(κ'/κ)) (H : Subgroup G) (hHK : H ≤ K)
    (hrel : 0 < H.relIndex K)
    (hclosed : ∀ U : Subgroup Gal(κ'/κ), U.FiniteIndex → IsClosed (U : Set Gal(κ'/κ))) :
    ∃ N : IntermediateField κ κ', FiniteDimensional κ ↥N ∧ Nonempty (H ≃* Gal(κ'/↥N)) := by
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
  -- The corresponding finite extension of `κ`.
  let N : IntermediateField κ κ' := IntermediateField.fixedField H'
  have hNfix : N.fixingSubgroup = H' := InfiniteGalois.fixingSubgroup_fixedField C
  haveI hNidx : N.fixingSubgroup.FiniteIndex := by rw [hNfix]; exact hH'fin
  haveI hNclosed : IsClosed (N.fixingSubgroup : Set Gal(κ'/κ)) := by
    rw [hNfix]; exact hH'closed
  -- Being closed of finite index, the fixing subgroup is open, i.e. `N` is finite over `κ`.
  have hNopen : IsOpen (N.fixingSubgroup : Set Gal(κ'/κ)) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _ (by assumption)
  have hNdim : FiniteDimensional κ ↥N :=
    (InfiniteGalois.isOpen_iff_finite N).mp hNopen
  refine ⟨N, hNdim, ?_⟩
  -- `H ≃ Ksub ≃ H' = N.fixingSubgroup ≃ Gal(κ'/N)`.
  have g : Ksub ≃* H' := Subgroup.equivMapOfInjective Ksub (e : K →* Gal(κ'/κ)) e.injective
  have g1 : Ksub ≃* H := Subgroup.subgroupOfEquivOfLe hHK
  exact ⟨(g1.symm.trans g).trans (hNfix.symm ▸ IntermediateField.fixingSubgroupEquiv N)⟩

theorem exists_intermediateField_of_le_stabilizer
    {K : Type u} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {K' : Type u} [Field K'] [Algebra K K'] [IsSepClosure K K']
    (A : ValuationSubring K') (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭)
    (hclosed_local : ∀ U : Subgroup
      (Gal(SeparableClosure (𝔭.adicCompletion K)/𝔭.adicCompletion K)),
      U.FiniteIndex → IsClosed (U : Set (Gal(SeparableClosure (𝔭.adicCompletion K)/
        𝔭.adicCompletion K))))
    (H : Subgroup Gal(K'/K)) (hHle : H ≤ MulAction.stabilizer Gal(K'/K) A)
    (hrel : 0 < H.relIndex (MulAction.stabilizer Gal(K'/K) A)) :
    ∃ (N : IntermediateField (𝔭.adicCompletion K) (SeparableClosure (𝔭.adicCompletion K))),
      FiniteDimensional (𝔭.adicCompletion K) ↥N ∧
        Nonempty (H ≃* Gal(SeparableClosure (𝔭.adicCompletion K)/↥N)) := by
  classical
  -- The decomposition group of the place `A` is the absolute Galois group of the completion.
  obtain ⟨e⟩ := NK.NeukirchUchida.nonempty_mulEquiv_decompositionGroupOf_localGalois
    (K := K) (K' := K') 𝔭 A hA
  exact exists_intermediateField_of_finiteIndex
    (K := MulAction.stabilizer Gal(K'/K) A) (e := e) H hHle hrel hclosed_local

end NK.LocalStructure.Brauer
