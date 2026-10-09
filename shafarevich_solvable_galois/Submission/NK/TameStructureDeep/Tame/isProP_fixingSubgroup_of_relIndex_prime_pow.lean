import Mathlib
import Submission.NK.TameStructureDeep.Tame.TameClosure
import Submission.NK.TameStructureDeep.Tame.isProPrimeToP_correctedWildInertia
import Submission.NK.TameStructureDeep.Support.isProP_of_openNormal_index
import Submission.NK.TameStructureDeep.Support.wildInertiaSubgroup_isClosed
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Pro-`p`-ness of the corrected wild inertia from the index condition on finite Galois layers

Let `κ = K_𝔭` be the `𝔭`-adic completion of a number field `K`, `p = resCharAt 𝔭` its residue
characteristic, `K'` a separable closure of `κ` and `T = κ^{tr} = tameClosure p π` the maximal
tamely ramified extension for a uniformiser `π`.  The *corrected wild inertia* is

  `V = V_κ = correctedWildInertia p π = Gal(K'/κ^{tr}) = T.fixingSubgroup`.

The arithmetic content of the theorem `V_κ` is pro-`p` is exactly the classical statement that the
wild inertia of a finite Galois extension of local fields is a `p`-group, in the form

  `h : [V_κ : V_κ ∩ Gal(K'/M)] = p ^ k`  for every finite dimensional Galois `M / κ`,

i.e. that the wild degree `[M : M ∩ κ^{tr}]` of a finite Galois layer is a power of `p`.  This file
shows that this index condition alone forces `NK.LocalTame.IsProP p ↥V_κ`.

The proof is the general profinite bookkeeping, with no further arithmetic:

* by `NK.TameStructureDeep.Support.isProP_of_openNormal_index` it suffices to test *open* normal
  subgroups `U ≤ ↥V_κ`; such a `U` is closed, so its image `H = U.map V.subtype` is a closed
  subgroup of `G_κ = Gal(K'/κ)` and `L = K'^H` is an intermediate field with `κ^{tr} ≤ L` and
  `[V_κ : U] = [L : κ^{tr}]` (`index_subgroupOf_fixingSubgroup`);
* `L/κ^{tr}` is finite, so by the primitive element theorem `L ⊆ κ^{tr} ⊔ M` for a *single* finite
  dimensional Galois `M/κ` — the splitting field of the minimal polynomial of a primitive element
  (`exists_finiteDimensional_isGalois_sup_of_le`, the classical fact that a finite separable
  extension is contained in a finite Galois one);
* hence `V_κ ∩ Gal(K'/M) ≤ H` and the index `[V_κ : U]` divides `[V_κ : V_κ ∩ Gal(K'/M)] = p ^ k`
  by `h`.
-/

open scoped Classical
open IntermediateField

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace NK.TameStructureDeep.Tame

noncomputable section

/-- **A finite separable extension is contained in a finite Galois extension, relative to a fixed
ambient field.**  For a separable extension `K'/κ` (here `K'` is a separable closure of `κ`) and
intermediate fields `T ≤ L` with `L/T` finite dimensional, there is a finite dimensional Galois
intermediate field `M/κ` with `L ≤ T ⊔ M`.

The proof takes a primitive element `α` of `L/T` (`L = T⟮α⟯`, primitive element theorem, using the
separability of `K'/κ`) and lets `M = κ(rootSet(minpoly κ α))`, the splitting field of the minimal
polynomial of `α`; it is finite dimensional and separable over `κ` (hence Galois), and contains
`α`, so that `T ⊔ M ⊇ T⟮α⟯ = L`. -/
theorem exists_finiteDimensional_isGalois_sup_of_le {κ K' : Type*} [Field κ] [Field K']
    [Algebra κ K'] [IsSepClosed K'] [Algebra.IsSeparable κ K']
    {T L : IntermediateField κ K'} (hTL : T ≤ L)
    [FiniteDimensional ↥T (IntermediateField.extendScalars hTL)] :
    ∃ M : IntermediateField κ K', FiniteDimensional κ M ∧ IsGalois κ M ∧ L ≤ T ⊔ M := by
  classical
  let L' : IntermediateField ↥T K' := IntermediateField.extendScalars hTL
  haveI hfd : FiniteDimensional ↥T ↥L' :=
    ‹FiniteDimensional ↥T (IntermediateField.extendScalars hTL)›
  haveI hsepT : Algebra.IsSeparable ↥T K' := Algebra.isSeparable_tower_top_of_isSeparable κ ↥T K'
  haveI hsepL : Algebra.IsSeparable ↥T ↥L' := Algebra.IsSeparable.of_algHom ↥T K' L'.val
  obtain ⟨α, hαtop⟩ := Field.exists_primitive_element ↥T ↥L'
  have hL'_eq : L' = IntermediateField.adjoin ↥T ({α.1} : Set K') := by
    rw [← IntermediateField.lift_adjoin_simple (F := ↥T) L' α, hαtop, IntermediateField.lift_top]
  let p : Polynomial κ := minpoly κ α.1
  let M : IntermediateField κ K' := IntermediateField.adjoin κ (p.rootSet K')
  have hpsplit : (p.map (algebraMap κ K')).Splits :=
    IsSepClosed.splits_codomain p (Algebra.IsSeparable.isSeparable κ α.1)
  haveI hMsplit : Polynomial.IsSplittingField κ ↥M p :=
    IntermediateField.adjoin_rootSet_isSplittingField hpsplit
  haveI hMfd : FiniteDimensional κ M := Polynomial.IsSplittingField.finiteDimensional ↥M p
  haveI hMgal : IsGalois κ M :=
    IsGalois.of_separable_splitting_field (Algebra.IsSeparable.isSeparable κ α.1)
  refine ⟨M, hMfd, hMgal, ?_⟩
  have hαM : α.1 ∈ M := by
    refine IntermediateField.subset_adjoin κ _ ?_
    rw [Polynomial.mem_rootSet]
    exact ⟨minpoly.ne_zero (Algebra.IsSeparable.isIntegral κ α.1), minpoly.aeval κ α.1⟩
  have hL'le : L' ≤ IntermediateField.extendScalars (le_sup_left : T ≤ T ⊔ M) := by
    rw [hL'_eq, IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    change α.1 ∈ (T ⊔ M : IntermediateField κ K')
    exact (le_sup_right (a := T) (b := M)) hαM
  intro x hx
  exact hL'le hx

theorem isProP_fixingSubgroup_of_relIndex_prime_pow {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    {π : 𝔭.adicCompletionIntegers K} (hπ : NK.TameStructureDeep.Tame.IsUniformizerAt 𝔭 π)
    (h : ∀ (M : IntermediateField (𝔭.adicCompletion K) K'),
      FiniteDimensional (𝔭.adicCompletion K) M → IsGalois (𝔭.adicCompletion K) M →
      ∃ k : ℕ,
        ((NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
              (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K)).fixingSubgroup ⊓
            M.fixingSubgroup).relIndex
          (NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
              (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K)).fixingSubgroup
          = (NK.TameStructureDeep.Tame.resCharAt 𝔭) ^ k) :
    NK.LocalTame.IsProP (NK.TameStructureDeep.Tame.resCharAt 𝔭)
      ↥(NK.TameStructureDeep.Tame.correctedWildInertia (κ := 𝔭.adicCompletion K) (K' := K')
        (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K)) := by
  classical
  have hp : (NK.TameStructureDeep.Tame.resCharAt 𝔭).Prime :=
    NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
  haveI hsepcl : IsSepClosed K' := IsSepClosure.sep_closed (𝔭.adicCompletion K)
  let T : IntermediateField (𝔭.adicCompletion K) K' :=
    NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
      (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K)
  let V : Subgroup (Gal(K'/𝔭.adicCompletion K)) := T.fixingSubgroup
  have hVcl : IsClosed (V : Set (Gal(K'/𝔭.adicCompletion K))) :=
    NK.TameStructure.ProfiniteAux.fixingSubgroup_isClosed_of_isIntegral T
  haveI : CompactSpace ↥V := isCompact_iff_compactSpace.mp hVcl.isCompact
  change NK.LocalTame.IsProP (NK.TameStructureDeep.Tame.resCharAt 𝔭) ↥V
  refine NK.TameStructureDeep.Support.isProP_of_openNormal_index hp ?_
  intro U
  haveI hUfi : (U : Subgroup ↥V).FiniteIndex := by
    rw [Subgroup.finiteIndex_iff_finite_quotient]
    exact Subgroup.quotient_finite_of_isOpen (U : Subgroup ↥V) U.isOpen
  have hUidxpos : 0 < (U : Subgroup ↥V).index :=
    Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero)
  have hUcV : IsClosed ((U : Subgroup ↥V) : Set ↥V) :=
    Subgroup.isClosed_of_isOpen _ U.isOpen
  let H : Subgroup (Gal(K'/𝔭.adicCompletion K)) := (U : Subgroup ↥V).map V.subtype
  have hHcl : IsClosed (H : Set (Gal(K'/𝔭.adicCompletion K))) := by
    have h1 : IsClosed (Subtype.val '' ((U : Subgroup ↥V) : Set ↥V)) :=
      hVcl.isClosedMap_subtype_val _ hUcV
    show IsClosed (((U : Subgroup ↥V).map V.subtype) : Set (Gal(K'/𝔭.adicCompletion K)))
    rw [Subgroup.coe_map]
    exact h1
  let L : IntermediateField (𝔭.adicCompletion K) K' := IntermediateField.fixedField H
  have hTL : T ≤ L := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup (k := 𝔭.adicCompletion K) T]
    exact fixedField_le (Subgroup.map_subtype_le (U : Subgroup ↥V))
  have hfix : H = L.fixingSubgroup :=
    (InfiniteGalois.fixingSubgroup_fixedField
      (⟨H, hHcl⟩ : ClosedSubgroup (Gal(K'/𝔭.adicCompletion K)))).symm
  have hUmap : H.subgroupOf V = (U : Subgroup ↥V) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hyx' : y = x := Subtype.ext hyx
      rwa [← hyx']
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hIdx : (U : Subgroup ↥V).index =
      Module.finrank ↥T (IntermediateField.extendScalars hTL) := by
    have h1 : (U : Subgroup ↥V).index = (L.fixingSubgroup.subgroupOf T.fixingSubgroup).index := by
      rw [← hUmap, hfix]
    rw [h1]
    exact index_subgroupOf_fixingSubgroup hTL
  haveI hfdTL : FiniteDimensional ↥T (IntermediateField.extendScalars hTL) := by
    rw [hIdx] at hUidxpos
    exact FiniteDimensional.of_finrank_pos hUidxpos
  obtain ⟨M, hMfd, hMgal, hLle⟩ :=
    exists_finiteDimensional_isGalois_sup_of_le (κ := 𝔭.adicCompletion K) (K' := K') hTL
  obtain ⟨k, hk⟩ := h M hMfd hMgal
  have hMinfle : V ⊓ M.fixingSubgroup ≤ H := by
    have h1 : V ⊓ M.fixingSubgroup = (T ⊔ M).fixingSubgroup := by
      rw [show V = T.fixingSubgroup from rfl, IntermediateField.fixingSubgroup_sup]
    rw [h1, hfix]
    exact IntermediateField.fixingSubgroup_le hLle
  have hdvd : (U : Subgroup ↥V).index ∣ (NK.TameStructureDeep.Tame.resCharAt 𝔭) ^ k := by
    have h2 : (V ⊓ M.fixingSubgroup).relIndex V = (NK.TameStructureDeep.Tame.resCharAt 𝔭) ^ k :=
      hk
    rw [← hUmap, ← h2]
    exact Subgroup.relIndex_dvd_of_le_left V hMinfle
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  exact ⟨j, hj⟩

end

end NK.TameStructureDeep.Tame
