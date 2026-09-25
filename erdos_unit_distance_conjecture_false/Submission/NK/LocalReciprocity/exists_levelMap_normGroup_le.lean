import Mathlib
import Submission.NK.LocalReciprocity.MaxAbelianSetup
import Submission.NK.LocalReciprocity.le_maxAbelianSubext_of_commutative

namespace NK.LocalReciprocity

universe u v

open scoped Classical

/-!
# Cofinality of the norm groups of the finite levels of `F^{ab}`

The existence theorem of local class field theory, as packaged in the `cofinal` field of the
reciprocity datum `LocalReciprocityDatum`, produces for every finite-index subgroup `M ≤ Fˣ` a
finite normal level `L` of `F'` with abelian Galois group and `N_{L/F} Lˣ ≤ M`.  Since such an `L`
is abelian over `F`, it lies in the maximal abelian subextension `F^{ab} = maxAbelianSubext F F'`
(`le_maxAbelianSubext_of_commutative`), so it can be regarded as a finite Galois level of the
*abelian* quotient `F^{ab}/F`.

This file performs precisely that regrading: given `N ≤ Fˣ` of finite index, it produces a
`FiniteGaloisIntermediateField F (maxAbelianSubext F F')` whose norm group —
`normGroup F ↥(levelMap L)`, computed after transporting the level inside `F'` — is contained
in `N`.  This is the cofinality input used to identify the profinite completion of `Fˣ` with
`Gal(F^{ab}/F)`.
-/

/-- **Cofinality of the levels of `F^{ab}`.**  For every finite-index normal subgroup `N ≤ Fˣ`
there is a finite Galois level `L` of the maximal abelian subextension `F^{ab} = maxAbelianSubext F F'`
whose norm group `N_{L/F} Lˣ` (viewed inside `F'`) is contained in `N`. -/
theorem exists_levelMap_normGroup_le {F : Type u} {F' : Type v} [Field F] [Field F']
    [Algebra F F'] [IsGalois F F'] (D : LocalReciprocityDatum F F')
    (N : FiniteIndexNormalSubgroup Fˣ) :
    ∃ L : FiniteGaloisIntermediateField F (maxAbelianSubext F F'),
      normGroup F ↥(levelMap (L : IntermediateField F (maxAbelianSubext F F'))) ≤ (N : Subgroup Fˣ) := by
  -- the existence theorem of local class field theory: an abelian finite level with small norm group
  obtain ⟨L, hfd, hnorm, hcomm, hle⟩ := D.cofinal (N : Subgroup Fˣ) N.isFiniteIndex'
  haveI : FiniteDimensional F ↥L := hfd
  haveI : Normal F ↥L := hnorm
  -- such a level is abelian over `F`, hence lies in the maximal abelian subextension
  have hLsub : L ≤ maxAbelianSubext F F' := le_maxAbelianSubext_of_commutative L hcomm
  -- regard the same level as a level of `F^{ab}` (i.e. pull it back along `F^{ab} ⊆ F'`)
  let L' : IntermediateField F (maxAbelianSubext F F') :=
    L.comap (IntermediateField.val (maxAbelianSubext F F'))
  -- transporting it back into `F'` recovers `L`
  have hlevelMap : levelMap L' = L := by
    refine le_antisymm ?_ ?_
    · intro x hx
      rw [mem_levelMap] at hx
      obtain ⟨y, hy⟩ := hx
      rw [← hy]
      exact y.2
    · intro x hx
      rw [mem_levelMap]
      exact ⟨⟨⟨x, hLsub hx⟩, hx⟩, rfl⟩
  -- `L` is separable over `F` because `F'` is, and normal by the existence theorem
  haveI : Algebra.IsSeparable F ↥L :=
    Algebra.isSeparable_tower_bot_of_isSeparable F ↥L F'
  haveI : IsGalois F ↥L := IsGalois.mk
  -- finiteness and Galois-ness transport along `L' ≃ₐ[F] levelMap L' = L`
  haveI : FiniteDimensional F ↥(levelMap L') := by rw [hlevelMap]; infer_instance
  haveI : FiniteDimensional F ↥L' :=
    FiniteDimensional.of_surjective (levelEquiv L').symm.toLinearMap (levelEquiv L').symm.surjective
  haveI : IsGalois F ↥(levelMap L') := by rw [hlevelMap]; infer_instance
  haveI : IsGalois F ↥L' := IsGalois.of_algEquiv (levelEquiv L').symm
  refine ⟨FiniteGaloisIntermediateField.mk L', ?_⟩
  show normGroup F ↥(levelMap L') ≤ (N : Subgroup Fˣ)
  rw [hlevelMap]
  exact hle

end NK.LocalReciprocity
