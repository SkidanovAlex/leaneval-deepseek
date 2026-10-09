import Mathlib
import Submission.NK.ReconstructField.LevelCandidate
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Enlarging a finite level so that its image under `ϕ` is Galois over `ℚ`

This file proves `NK.ReconstructField.exists_level_galois_image`, the step of the Neukirch–Uchida
reconstruction (§12.2) that allows the Čebotarev-type arguments to be run on levels of `K₁'` whose
image `levelMap ϕ L'` is a *Galois extension of `ℚ`*.

Given a finite normal level `L ⊆ K₁'` (with `↥L` a number field), we produce a larger finite normal
level `L' ⊇ L` such that `levelMap ϕ L'` is Galois over `ℚ`.  The construction is the natural one:

* `N := levelMap ϕ L` is a finite extension of `K₂` (indeed a number field, normal over `K₂`);
* take `M₀` to be the **normal closure over `ℚ`** of `N` inside `K₂'`, i.e.
  `M₀ = IntermediateField.normalClosure ℚ ↥N K₂'`; it is finite over `ℚ`, and — being the normal
  closure — it is normal over `ℚ`; since `ℚ` has characteristic zero it is Galois over `ℚ`;
* being normal over `ℚ` and containing `K₂`, `M₀` is normal over `K₂` as well
  (`Normal.tower_top_of_normal`), so its preimage level `L' := levelMap ϕ.symm M₀` is normal over
  `K₁`;
* `L ≤ L'` because `levelMap ϕ L = N ⊆ M₀ = levelMap ϕ L'`.

`K₂` is a number field, hence `K₂'` is an algebraically closed field of characteristic zero and in
particular `Algebra ℚ K₂'` is available; the file records the small `CharZero` instance needed to
make the `ℚ`-structure on `K₂'` (and on its subfields) available to type class inference.
-/

set_option linter.style.haveILetI false

namespace NK.ReconstructField

open NK.Reconstruct
open scoped Pointwise

/-- **`levelMap` is monotone**: a larger level has a larger image under the correspondence of `ϕ`.
(Proved by unfolding the definition and using `mem_levelMap_iff`.) -/
theorem levelMap_monotone {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) {L L' : IntermediateField K₁ K₁'} (h : L ≤ L') :
    levelMap ϕ L ≤ levelMap ϕ L' := by
  intro x hx
  rw [mem_levelMap_iff] at hx ⊢
  intro g hg
  exact hx g (fun y => hg ⟨(y : K₁'), h y.2⟩)

/-- **The level correspondence of `ϕ` is inverted by that of `ϕ.symm`**: for a finite level
`M ⊆ K₂'`, `levelMap ϕ (levelMap ϕ.symm M) = M`.

Both maps are the fixed-field correspondence, and on finite levels the `fixingSubgroup`/`fixedField`
adjunction is an equivalence (`InfiniteGalois.fixedField_fixingSubgroup`). -/
theorem levelMap_levelMap_symm {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (M : IntermediateField K₂ K₂') [FiniteDimensional K₂ M] :
    levelMap ϕ (levelMap ϕ.symm M) = M := by
  haveI : IsGalois K₂ K₂' := IsSepClosure.isGalois
  have hsymm : IsHomeomorph (ϕ.symm : Gal(K₂'/K₂) → Gal(K₁'/K₁)) :=
    Submission.NeukirchUchida.isHomeomorph_symm ϕ hϕ
  rw [levelMap]
  rw [fixingSubgroup_levelMap hsymm M]
  rw [Subgroup.map_map]
  have hcomp : ((ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)).comp (ϕ.symm : Gal(K₂'/K₂) →* Gal(K₁'/K₁)))
      = MonoidHom.id _ := by
    ext g x
    simp
  rw [hcomp, Subgroup.map_id]
  exact InfiniteGalois.fixedField_fixingSubgroup M

/-- The other direction of the round trip: `levelMap ϕ.symm (levelMap ϕ L) = L` for a finite level
`L ⊆ K₁'`.  This is `levelMap_levelMap_symm` applied to `ϕ.symm`. -/
theorem levelMap_symm_levelMap {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] :
    levelMap ϕ.symm (levelMap ϕ L) = L :=
  levelMap_levelMap_symm ϕ.symm (Submission.NeukirchUchida.isHomeomorph_symm ϕ hϕ) L

/-- `K₂'` has characteristic zero, being an extension of the number field `K₂`. -/
theorem charZero_of_isSepClosure (K₂ : Type*) {K₂' : Type*} [Field K₂] [Field K₂']
    [NumberField K₂] [Algebra K₂ K₂'] : CharZero K₂' := by
  refine ⟨fun m n h => ?_⟩
  have h' : algebraMap K₂ K₂' (m : K₂) = algebraMap K₂ K₂' (n : K₂) := by simpa using h
  exact Nat.cast_injective (RingHom.injective (algebraMap K₂ K₂') h')

/-- **Every finite normal level `L ⊆ K₁'` can be enlarged to a finite normal level `L'` whose image
under `ϕ` is Galois over `ℚ`.** -/
theorem exists_level_galois_image {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂]
    [Field K₁'] [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L] [NumberField ↥L] :
    ∃ (L' : IntermediateField K₁ K₁') (_ : FiniteDimensional K₁ L') (_ : Normal K₁ L')
      (_ : NumberField ↥L'),
      L ≤ L' ∧ IsGalois ℚ ↥(NK.Reconstruct.levelMap ϕ L') := by
  -- `ℚ`-structure on `K₂'` and on its intermediate fields
  haveI hgc : CharZero K₂' := charZero_of_isSepClosure K₂
  haveI hstQ : IsScalarTower ℚ K₂ K₂' := inferInstance
  haveI hG₂ : IsGalois K₂ K₂' := IsSepClosure.isGalois
  haveI hssc : IsSepClosed K₂' := IsSepClosure.sep_closed K₂
  have hsymm : IsHomeomorph (ϕ.symm : Gal(K₂'/K₂) → Gal(K₁'/K₁)) :=
    Submission.NeukirchUchida.isHomeomorph_symm ϕ hϕ
  -- the image `N` of `L`, a finite normal number-field level of `K₂'`
  let N : IntermediateField K₂ K₂' := levelMap ϕ L
  haveI hNnf : NumberField ↥N := numberField_levelMap hϕ L
  haveI hNfin : FiniteDimensional K₂ N := finiteDimensional_levelMap hϕ L
  haveI hNalgQ : Algebra.IsAlgebraic ℚ ↥N := inferInstance
  haveI hNsepQ : Algebra.IsSeparable ℚ ↥N := inferInstance
  -- the normal closure `M₀` of `N` over `ℚ` inside `K₂'`
  let M₀ : IntermediateField ℚ K₂' := IntermediateField.normalClosure ℚ ↥N K₂'
  haveI hMfin₀ : FiniteDimensional ℚ ↥M₀ := inferInstance
  haveI hNC : IsNormalClosure ℚ ↥N M₀ :=
    Algebra.IsAlgebraic.isNormalClosure_normalClosure (splits := fun x =>
      IsSepClosed.splits_codomain (minpoly ℚ x) (Algebra.IsSeparable.isSeparable ℚ x))
  haveI hnormM₀ : Normal ℚ ↥M₀ := hNC.normal
  haveI hgalM₀ : IsGalois ℚ ↥M₀ := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  -- `N ≤ M₀`, viewed over `ℚ`
  have hNM : (N : Set K₂') ⊆ (M₀ : Set K₂') := by
    let N₀ : IntermediateField ℚ K₂' := N.toSubfield.toIntermediateField (fun q => by
      rw [IsScalarTower.algebraMap_apply ℚ K₂ K₂']
      exact IntermediateField.algebraMap_mem N (algebraMap ℚ K₂ q))
    have hN₀ : N₀ ≤ M₀ := IntermediateField.le_normalClosure N₀
    intro x hx
    exact hN₀ hx
  -- the same subfield of `K₂'`, now viewed as an intermediate field of `K₂'/K₂`
  let M : IntermediateField K₂ K₂' := M₀.toSubfield.toIntermediateField
    (fun x => hNM (IntermediateField.algebraMap_mem N x))
  haveI hstM : IsScalarTower ℚ K₂ ↥M := inferInstance
  haveI hMfinQ : Module.Finite ℚ ↥M := hMfin₀
  haveI hMfin : FiniteDimensional K₂ M := Module.Finite.of_restrictScalars_finite ℚ K₂ ↥M
  haveI hnormM : Normal ℚ ↥M := hnormM₀
  haveI hnormK₂M : Normal K₂ M := Normal.tower_top_of_normal ℚ K₂ ↥M
  haveI hgalM : IsGalois ℚ ↥M := hgalM₀
  -- the enlarged level is the preimage of `M`
  refine ⟨levelMap ϕ.symm M, finiteDimensional_levelMap hsymm M, normal_levelMap hsymm M,
    numberField_levelMap hsymm M, ?_, ?_⟩
  · have h₁ : levelMap ϕ L ≤ M := hNM
    have h₂ : levelMap ϕ.symm (levelMap ϕ L) ≤ levelMap ϕ.symm M := levelMap_monotone ϕ.symm h₁
    rwa [levelMap_symm_levelMap ϕ hϕ L] at h₂
  · rw [levelMap_levelMap_symm ϕ hϕ M]
    exact hgalM

end NK.ReconstructField
