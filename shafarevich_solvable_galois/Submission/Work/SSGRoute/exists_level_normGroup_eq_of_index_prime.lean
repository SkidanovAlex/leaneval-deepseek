import Mathlib
import Submission.Work.SSGRoute.LocalCFTAggregatorDefs
import Submission.NK.LocalCFT.NormGroup.normGroup_eq_iff
import Submission.NK.LocalArtin.Reduction.kernelCondition_toReciprocityMap
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open CategoryTheory

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

section Aux

variable {F : Type*} {F' : Type*} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']

/-- **The norm-group correspondence, existence form.**  For a field `F` with Galois extension `F'`
carrying a local Artin reciprocity datum `D`, every finite-index subgroup `U ≤ Fˣ` is the norm
group `N_{L'/F} L'ˣ` of a finite Galois level `L' ≤ F^{ab}`, of degree equal to the index.

Route: `D.cofinal` supplies a finite abelian level `L ≤ F^{ab}` with `N_{L/F} Lˣ ≤ U`; the norm
group at `L` is the kernel of the Artin map `ψ : Fˣ →* Gal(L/F)`, so `U = ψ⁻¹(ψ(U))`; the preimage
`S ≤ Gal(F^{ab}/F)` of the subgroup `ψ(U) ≤ Gal(L/F)` is open (it contains the open subgroup
`Gal(F^{ab}/L)`) hence closed, and `U = S.comap D.artin`; the fixed field `L'` of `S` satisfies
`L'.fixingSubgroup = S`, whence `N_{L'/F} L'ˣ = S.comap D.artin = U` by
`normGroup_eq_iff_comap_fixingSubgroup`, and `Gal(L'/F) ≅ Gal(F^{ab}/F)/S` has `S.index = U.index`
elements. -/
theorem exists_level_normGroup_eq_of_finiteIndex (D : NK.LocalCFT.ArtinReciprocity F F')
    (U : Subgroup Fˣ) (hU : U.FiniteIndex) :
    ∃ (L' : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F')),
      FiniteDimensional F ↥L' ∧ IsGalois F ↥L' ∧
      NK.LocalReciprocity.normGroup F ↥L' = U ∧
      Nat.card (↥L' ≃ₐ[F] ↥L') = U.index := by
  obtain ⟨L, hLfd, hLn, hLcomm, hNL⟩ := D.cofinal U hU
  haveI : FiniteDimensional F ↥L := hLfd
  haveI : Normal F ↥L := hLn
  -- the Artin map at the level `L`
  let ψ : Fˣ →* (↥L ≃ₐ[F] ↥L) := (NK.LocalCFT.levelRestrict L).comp D.artin
  have hψsurj : Function.Surjective ψ := (D.isLevelIso L hLcomm).1
  have hψker : ψ.ker = NK.LocalReciprocity.normGroup F ↥L := (D.isLevelIso L hLcomm).2
  -- the subgroup of the finite level group, and its preimage in `Gal(F^{ab}/F)`
  let H : Subgroup (↥L ≃ₐ[F] ↥L) := U.map ψ
  let S : Subgroup (NK.LocalReciprocity.maxAbelianSubext F F' ≃ₐ[F]
      NK.LocalReciprocity.maxAbelianSubext F F') := H.comap (NK.LocalCFT.levelRestrict L)
  -- `S` contains the open subgroup `Gal(F^{ab}/L) = L.fixingSubgroup`, so it is closed
  have hLfix_le_S : L.fixingSubgroup ≤ S := by
    rw [← IntermediateField.restrictNormalHom_ker L]
    exact MonoidHom.ker_le_comap _ H
  have hSopen : IsOpen (S : Set (NK.LocalReciprocity.maxAbelianSubext F F' ≃ₐ[F]
      NK.LocalReciprocity.maxAbelianSubext F F')) :=
    Subgroup.isOpen_mono hLfix_le_S (IntermediateField.fixingSubgroup_isOpen L)
  have hSclosed : IsClosed (S : Set (NK.LocalReciprocity.maxAbelianSubext F F' ≃ₐ[F]
      NK.LocalReciprocity.maxAbelianSubext F F')) := Subgroup.isClosed_of_isOpen S hSopen
  -- `Gal(F^{ab}/F)` is abelian, so every subgroup is normal
  have hSnorm : S.Normal :=
    Subgroup.Normal.mk fun n hn g => by
      rw [NK.LocalReciprocity.commutative_gal_maxAbelianSubext g n, mul_assoc, mul_inv_cancel,
        mul_one]
      exact hn
  -- the fixed field of `S`
  let L' : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F') :=
    IntermediateField.fixedField S
  have hL'fix : L'.fixingSubgroup = S :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨S, hSclosed⟩
  have hGal : IsGalois F ↥L' := by
    refine (InfiniteGalois.normal_iff_isGalois L').mp ?_
    rw [hL'fix]
    exact hSnorm
  -- the index of `S` is the index of `U`
  have hSidx : S.index = H.index :=
    Subgroup.index_comap_of_surjective H (by
      rw [NK.LocalCFT.levelRestrict]
      exact AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := ↥L)
        (NK.LocalReciprocity.maxAbelianSubext F F'))
  have hHidx : H.index = U.index :=
    Subgroup.index_map_eq U hψsurj (by rw [hψker]; exact hNL)
  -- hence `Gal(L'/F)` has `U.index` elements
  have hcard : Nat.card (↥L' ≃ₐ[F] ↥L') = U.index := by
    haveI : S.Normal := hSnorm
    have hiso := InfiniteGalois.normalAutEquivQuotient (k := F)
      (K := NK.LocalReciprocity.maxAbelianSubext F F') ⟨S, hSclosed⟩
    calc Nat.card (↥L' ≃ₐ[F] ↥L')
        = Nat.card (((NK.LocalReciprocity.maxAbelianSubext F F') ≃ₐ[F]
            (NK.LocalReciprocity.maxAbelianSubext F F')) ⧸ S) :=
          (Nat.card_congr hiso.toEquiv).symm
      _ = S.index := (Subgroup.index_eq_card S).symm
      _ = U.index := by rw [hSidx, hHidx]
  have hFinAut : Finite (↥L' ≃ₐ[F] ↥L') :=
    (Nat.card_ne_zero.mp (by rw [hcard]; exact hU.index_ne_zero)).2
  have hFinL' : FiniteDimensional F ↥L' := by
    haveI : IsGalois F ↥L' := hGal
    haveI : Finite (↥L' ≃ₐ[F] ↥L') := hFinAut
    exact IsGalois.finiteDimensional_of_finite F ↥L'
  -- the norm group of `L'` is `U`
  have hnorm : NK.LocalReciprocity.normGroup F ↥L' = U := by
    haveI : FiniteDimensional F ↥L' := hFinL'
    haveI : Normal F ↥L' := hGal.to_normal
    rw [NK.LocalCFT.NormGroup.normGroup_eq_iff_comap_fixingSubgroup D L', hL'fix]
    ext x
    constructor
    · intro hx
      have hx' : ψ x ∈ U.map ψ := hx
      rw [Subgroup.mem_map] at hx'
      obtain ⟨u, hu, hux⟩ := hx'
      have hmem : x * u⁻¹ ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hux, mul_inv_cancel]
      rw [hψker] at hmem
      have hmemU : x * u⁻¹ ∈ U := hNL hmem
      have hxeq : x = (x * u⁻¹) * u := by group
      rw [hxeq]
      exact mul_mem hmemU hu
    · intro hx
      exact Subgroup.mem_map_of_mem ψ hx
  exact ⟨L', hFinL', hGal, hnorm, hcard⟩

end Aux

/-- **Every subgroup of prime index of `Fˣ` is a norm group** (`F = Q.adicCompletion K`).

For a number field `K`, a finite place `Q` of `K` with completion `F = Q.adicCompletion K`, a prime
`p` and a subgroup `U ≤ Fˣ` of index `p`, there is a finite Galois extension `E/F` of degree `p`
whose norm group is exactly `U`:

  `∃ E/F, Nat.card (E ≃ₐ[F] E) = p ∧ NK.LocalReciprocity.normGroup F E = U`.

This is the "existence + correspondence" half of local class field theory at index `p`: the norm
group correspondence `L ↦ N_{L/F}Lˣ` is a bijection from the finite abelian levels of `F^{ab}` onto
the open finite-index subgroups of `Fˣ`.  Route: `NK.NUV2.Final.nonempty_kernelCondition_of_L7`
(`KernelCondition`, proved unconditionally),
`NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion` (the norm index theorem
`[Fˣ : N_{L/F}Lˣ] = [L:F]`), hence a `ReciprocityMap`
(`NK.LocalArtin.Reduction.kernelCondition_toReciprocityMap`) giving the surjectivity and the kernel
of the Artin map at every finite abelian level; the existence theorem
(`NK.LocalReciprocityLubinTate.existenceTheorem_adicCompletion`) provides a level `L` with
`N_L ≤ U`; the preimage under the level reciprocity isomorphism `Fˣ ⧸ N_L ≃* Gal(L/F)` of the
subgroup `U ⧸ N_L ≤ Gal(L/F)` is the fixing subgroup of a subfield `L' ⊆ L` with
`N_{L'} = U` and `[L' : F] = [Fˣ : U] = p`. -/
theorem exists_level_normGroup_eq_of_index_prime {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (p : ℕ) [Fact p.Prime] (U : Subgroup (Q.adicCompletion K)ˣ) (hU : U.index = p) :
    ∃ (E : Type) (_ : Field E) (_ : Algebra (Q.adicCompletion K) E)
      (_ : FiniteDimensional (Q.adicCompletion K) E) (_ : IsGalois (Q.adicCompletion K) E),
      Nat.card (E ≃ₐ[Q.adicCompletion K] E) = p ∧
        NK.LocalReciprocity.normGroup (Q.adicCompletion K) E = U := by
  obtain ⟨hKC⟩ := NK.NUV2.Final.nonempty_kernelCondition_of_L7 Q
  have hN := NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion Q
  have hex := NK.LocalReciprocityLubinTate.existenceTheorem_adicCompletion Q
  obtain ⟨R⟩ := NK.LocalArtin.Reduction.kernelCondition_toReciprocityMap hKC hN
  let D : NK.LocalCFT.ArtinReciprocity (Q.adicCompletion K)
      (SeparableClosure (Q.adicCompletion K)) := R.toArtinReciprocity hex
  have hUfin : U.FiniteIndex := by
    rw [Subgroup.finiteIndex_iff, hU]
    exact (Fact.out : p.Prime).ne_zero
  obtain ⟨L', hfd, hgal, hnorm, hcard⟩ :=
    exists_level_normGroup_eq_of_finiteIndex (F := Q.adicCompletion K)
      (F' := SeparableClosure (Q.adicCompletion K)) D U hUfin
  refine ⟨↥L', inferInstance, inferInstance, hfd, hgal, ?_, hnorm⟩
  rw [hcard, hU]

end Work.SSGRoute
