import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.t0Generation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open _root_.SSGRoute
open scoped Pointwise

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

/-- **The `T⁰`-generation of a subgroup of a finite quotient of `G_ℚ`, with cyclic pieces.**

Let `Γ` be a finite group, `ψ : G_ℚ →* Γ` a continuous surjection (equivalently: with open kernel)
and `H ≤ Γ`.  Then there is a finite set `T⁰` of places of `ℚ̄` whose `ψ`-images of decomposition
groups generate `H`, lie in `H`, and each of which is *cyclic*.

The construction is that of `Work.SSGRoute.t0Generation`: the places are indexed by the elements
`σ` of `H_L = (H.comap ψ).map (restrictNormalHom L)` where `L` is the field cut out by `ker ψ`;
for each `σ` Chebotarev (`Work.SSGRoute.t0_placeDecompImage`) produces a place `A_σ` with
`(decomp ℚ A_σ).map (restrictNormalHom L) = zpowers σ`, so

`(decomp ℚ A_σ).map ψ = zpowers (ψbar σ)`,

the image of a single element, hence cyclic. -/
theorem t0Generation_cyclic_strong (Γ : Type*) [Group Γ] [Finite Γ] (ψ : SSGRoute.GalQ →* Γ)
    (hopen : IsOpen (ψ.ker : Set SSGRoute.GalQ)) (hsurj : Function.Surjective ψ)
    (H : Subgroup Γ) :
    ∃ T0 : Finset (ValuationSubring SSGRoute.QBar),
      (∀ A ∈ T0, (SSGRoute.decomp ℚ A).map ψ ≤ H) ∧
      (⨆ A ∈ T0, (SSGRoute.decomp ℚ A).map ψ) = H ∧
      (∀ A ∈ T0, IsCyclic ((SSGRoute.decomp ℚ A).map ψ)) := by
  classical
  haveI hAlgClosure : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ
  haveI hGalQ : IsGalois ℚ SSGRoute.QBar :=
    { to_isSeparable := inferInstance, to_normal := inferInstance }
  have hclosed : IsClosed (ψ.ker : Set SSGRoute.GalQ) := Subgroup.isClosed_of_isOpen ψ.ker hopen
  let L : IntermediateField ℚ SSGRoute.QBar := IntermediateField.fixedField ψ.ker
  have hLfix : L.fixingSubgroup = ψ.ker := by
    have h := InfiniteGalois.fixingSubgroup_fixedField (k := ℚ) (K := AlgebraicClosure ℚ)
      (⟨ψ.ker, hclosed⟩ : ClosedSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    simpa [L] using h
  have hLfd : FiniteDimensional ℚ L :=
    (InfiniteGalois.isOpen_iff_finite (k := ℚ) (K := AlgebraicClosure ℚ) L).mp (hLfix ▸ hopen)
  haveI hLfdI : FiniteDimensional ℚ L := hLfd
  haveI hLgal : IsGalois ℚ L :=
    IsGalois.of_fixedField_normal_subgroup (K := ℚ) (L := AlgebraicClosure ℚ) ψ.ker
      (hn := MonoidHom.normal_ker ψ)
  haveI hLnf : NumberField ↥L := inferInstance
  have hrker : (AlgEquiv.restrictNormalHom L).ker = ψ.ker := by
    rw [IntermediateField.restrictNormalHom_ker, hLfix]
  obtain ⟨ψbar, hψbar⟩ := t0_restrictLift L ψ hrker.symm
  let HL : Subgroup (↥L ≃ₐ[ℚ] ↥L) := (H.comap ψ).map (AlgEquiv.restrictNormalHom L)
  have hHmap : HL.map ψbar = H := by
    show Subgroup.map ψbar
        (Subgroup.map (AlgEquiv.restrictNormalHom L) (Subgroup.comap ψ H)) = H
    rw [Subgroup.map_map, hψbar, Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr hsurj, top_inf_eq]
  have hc : NK.Reconstruct.ChebotarevInput ℚ SSGRoute.QBar := by
    haveI : IsSepClosure ℚ SSGRoute.QBar := inferInstance
    exact (NK.ReconstructEndgame.chebotarevInput_congr ℚ SSGRoute.QBar).mpr
      ((NK.NUV2.chebotarev_all0 NK.CFTLib.fundamentalClassElement) ℚ SSGRoute.QBar)
  have key : ∀ σ : ↥HL, ∃ A : ValuationSubring SSGRoute.QBar,
      (SSGRoute.decomp ℚ A).map (AlgEquiv.restrictNormalHom L) =
        Subgroup.zpowers (σ : ↥L ≃ₐ[ℚ] ↥L) :=
    fun σ => (t0_placeDecompImage hc L (σ : ↥L ≃ₐ[ℚ] ↥L)).imp (fun A h => h.2)
  let Afun : ↥HL → ValuationSubring SSGRoute.QBar := fun σ => Classical.choose (key σ)
  have hAfun : ∀ σ : ↥HL, (SSGRoute.decomp ℚ (Afun σ)).map (AlgEquiv.restrictNormalHom L) =
        Subgroup.zpowers (σ : ↥L ≃ₐ[ℚ] ↥L) := fun σ => Classical.choose_spec (key σ)
  have hval : ∀ σ : ↥HL, (SSGRoute.decomp ℚ (Afun σ)).map ψ =
      Subgroup.zpowers (ψbar (σ : ↥L ≃ₐ[ℚ] ↥L)) := by
    intro σ
    rw [← hψbar, ← Subgroup.map_map, hAfun σ, t0_map_zpowers]
  refine ⟨Finset.univ.image Afun, ?_, ?_, ?_⟩
  · intro A' hA'
    rw [Finset.mem_image] at hA'
    obtain ⟨σ, -, rfl⟩ := hA'
    rw [hval σ]
    exact Subgroup.zpowers_le.mpr (hHmap ▸ Subgroup.mem_map.mpr ⟨σ, σ.2, rfl⟩)
  · rw [← Finset.sup_eq_iSup, Finset.sup_image]
    show Finset.univ.sup (fun σ : ↥HL => (SSGRoute.decomp ℚ (Afun σ)).map ψ) = H
    have hsup_eq : (Finset.univ.sup (fun σ : ↥HL =>
        Subgroup.zpowers (ψbar (σ : ↥L ≃ₐ[ℚ] ↥L)))) = H := by
      apply le_antisymm
      · apply Finset.sup_le
        intro σ _
        exact Subgroup.zpowers_le.mpr (hHmap ▸ Subgroup.mem_map.mpr ⟨σ, σ.2, rfl⟩)
      · intro h hh
        rw [← hHmap, Subgroup.mem_map] at hh
        obtain ⟨σ, hσ, rfl⟩ := hh
        exact Finset.le_sup (f := fun σ : ↥HL =>
            Subgroup.zpowers (ψbar (σ : ↥L ≃ₐ[ℚ] ↥L))) (Finset.mem_univ ⟨σ, hσ⟩)
          (Subgroup.mem_zpowers (ψbar (σ : ↥L ≃ₐ[ℚ] ↥L)))
    rw [show (fun σ : ↥HL => (SSGRoute.decomp ℚ (Afun σ)).map ψ) =
        (fun σ : ↥HL => Subgroup.zpowers (ψbar (σ : ↥L ≃ₐ[ℚ] ↥L))) from funext hval]
    exact hsup_eq
  · intro A' hA'
    rw [Finset.mem_image] at hA'
    obtain ⟨σ, -, rfl⟩ := hA'
    rw [hval σ]
    infer_instance

theorem t0Generation_cyclic (Γ : Type*) [Group Γ] [Finite Γ] (ψ : SSGRoute.GalQ →* Γ)
    (hopen : IsOpen (ψ.ker : Set SSGRoute.GalQ)) (hsurj : Function.Surjective ψ)
    (H : Subgroup Γ) :
    ∃ T0 : Finset (ValuationSubring SSGRoute.QBar),
      (⨆ A ∈ T0, (SSGRoute.decomp ℚ A).map ψ) = H ∧
      (∀ A ∈ T0, IsCyclic ((SSGRoute.decomp ℚ A).map ψ)) := by
  obtain ⟨T0, -, hgen, hcyc⟩ := t0Generation_cyclic_strong Γ ψ hopen hsurj H
  exact ⟨T0, hgen, hcyc⟩

end Work.SSGRoute
