import Mathlib
import Submission.Work.SSGRoute.E7bDefs
import Submission.Work.SSGRoute.decompK_restrict_exists
import Submission.Work.SSGRoute.localUnitsMap_exists
import Submission.Work.SSGRoute.ext_corestriction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open SSGRoute.PTExt CategoryTheory

set_option maxHeartbeats 1600000
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.SSGRoute.Y3Dev

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module
attribute [local instance 1] ULift.module ULift.smulLeft ULift.mulAction ULift.smulZeroClass
attribute [local instance 1] ULift.distribSMul ULift.distribMulAction ULift.smulWithZero
attribute [local instance 1] ULift.mulActionWithZero

variable (k k' K : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] [Field K]
  [NumberField K] [Algebra k K] [Algebra k' K] [Algebra k k'] [IsScalarTower k k' K]
  [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k' K] [IsGalois k' K]

noncomputable def baseChangeSubgroup (w : NK.GlobalCFT.Place K) : Subgroup (decompK (k := k) w) :=
  ((decompK (k := k') w).map (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K))).comap
    (decompK (k := k) w).subtype

theorem restrictScalars_smul_place_K (σ : K ≃ₐ[k'] K) (w : NK.GlobalCFT.Place K) :
    AlgEquiv.restrictScalars k σ • w = σ • w := by
  cases w with
  | inl w => rfl
  | inr q => rfl

theorem map_le_decompK (w : NK.GlobalCFT.Place K) :
    (decompK (k := k') w).map (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K))
      ≤ decompK (k := k) w := by
  intro σ hσ
  rw [Subgroup.mem_map] at hσ
  obtain ⟨τ, hτ, rfl⟩ := hσ
  rw [MulAction.mem_stabilizer_iff] at hτ ⊢
  rw [show (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K)) τ
      = AlgEquiv.restrictScalars k τ from rfl]
  rw [restrictScalars_smul_place_K k k' K]
  exact hτ

noncomputable def baseChangeMulEquiv (w : NK.GlobalCFT.Place K) :
    decompK (k := k') w ≃* baseChangeSubgroup k k' K w :=
  (Subgroup.equivMapOfInjective (decompK (k := k') w)
      (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K))
      (AlgEquiv.restrictScalars_injective k)).trans
    ((Subgroup.subgroupOfEquivOfLe (map_le_decompK k k' K w)).symm)

/-- The `M`-coefficient change of base field at the base level. -/
theorem rep_res_baseChangeMulEquiv_M (w : NK.GlobalCFT.Place K) (M : Rep Coeff (K ≃ₐ[k] K)) :
    Rep.res (baseChangeMulEquiv k k' K w).toMonoidHom
        (Rep.res (baseChangeSubgroup k k' K w).subtype (Rep.res (decompK (k := k) w).subtype M))
      = Rep.res (decompK (k := k') w).subtype
          (Rep.res (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K)) M) := rfl

/-- The local-units change of base field at the base level. -/
theorem rep_res_baseChangeMulEquiv_localUnits (w : NK.GlobalCFT.Place K) :
    Rep.res (baseChangeMulEquiv k k' K w).toMonoidHom
        (Rep.res (baseChangeSubgroup k k' K w).subtype (localUnitsK (k := k) w))
      = localUnitsK (k := k') w := rfl

/-- The canonical map `H' →* H` of stabilizers. -/
noncomputable def thetaLMap (k k' L : Type) [Field k] [NumberField k] [Field k'] [NumberField k']
    [Field L] [NumberField L]
    [Algebra k L] [Algebra k' L] [Algebra k k'] [IsScalarTower k k' L] (w' : NK.GlobalCFT.Place L) :
    MulAction.stabilizer (L ≃ₐ[k'] L) w' →* MulAction.stabilizer (L ≃ₐ[k] L) w' :=
  MonoidHom.codRestrict
    ((AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := L)).comp
      (MulAction.stabilizer (L ≃ₐ[k'] L) w').subtype)
    (MulAction.stabilizer (L ≃ₐ[k] L) w') (fun σ => by
      rw [MulAction.mem_stabilizer_iff]
      rw [show ((AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := L)).comp
          (MulAction.stabilizer (L ≃ₐ[k'] L) w').subtype) σ
          = AlgEquiv.restrictScalars k (σ : L ≃ₐ[k'] L) from rfl]
      rw [show AlgEquiv.restrictScalars k (σ : L ≃ₐ[k'] L) • w' = (σ : L ≃ₐ[k'] L) • w' from by
        cases w' <;> rfl]
      exact MulAction.mem_stabilizer_iff.mp σ.2)

section Level

variable (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [FiniteDimensional k L] [IsGalois k L] [Algebra k' L] [IsScalarTower k' K L]
  [IsScalarTower k k' L] [FiniteDimensional k' L] [IsGalois k' L]
  (w' : NK.GlobalCFT.Place L)

theorem restrictScalars_smul_place_L (σ : L ≃ₐ[k'] L) :
    AlgEquiv.restrictScalars k σ • w' = σ • w' := by
  cases w' with
  | inl w => rfl
  | inr q => rfl

theorem galRes_restrictScalars :
    (galRes k K L).comp (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := L))
      = (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K)).comp (galRes k' K L) := by
  refine MonoidHom.ext fun σ => AlgEquiv.ext fun x => ?_
  apply (algebraMap K L).injective
  show algebraMap K L (((AlgEquiv.restrictScalars k σ).restrictNormal K) x)
      = algebraMap K L ((σ.restrictNormal K) x)
  rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.restrictNormal_commutes]
  rfl

theorem thetaLMap_apply (σ : MulAction.stabilizer (L ≃ₐ[k'] L) w') :
    ((thetaLMap k k' L w' σ : MulAction.stabilizer (L ≃ₐ[k] L) w') : L ≃ₐ[k] L)
      = AlgEquiv.restrictScalars k (σ : L ≃ₐ[k'] L) := rfl

/-- The canonical map `D_{w'}(L/k') →* S.comap f`. -/
noncomputable def betaMap (w : NK.GlobalCFT.Place K)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
    (f' : MulAction.stabilizer (L ≃ₐ[k'] L) w' →* decompK (k := k') w)
    (hf' : ∀ σ, ((f' σ : decompK (k := k') w) : K ≃ₐ[k'] K) = galRes k' K L (σ : L ≃ₐ[k'] L)) :
    MulAction.stabilizer (L ≃ₐ[k'] L) w' →* (baseChangeSubgroup k k' K w).comap f :=
  MonoidHom.codRestrict (thetaLMap k k' L w')
    ((baseChangeSubgroup k k' K w).comap f) (fun σ => by
      rw [Subgroup.mem_comap]
      refine Subgroup.mem_map.mpr ⟨(f' σ : decompK (k := k') w), (f' σ).2, ?_⟩
      show (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K))
            ((f' σ : decompK (k := k') w) : K ≃ₐ[k'] K)
        = (f (thetaLMap k k' L w' σ) : K ≃ₐ[k] K)
      rw [hf (thetaLMap k k' L w' σ), hf' σ]
      rw [thetaLMap_apply]
      rw [show (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K))
            ((galRes k' K L) (σ : L ≃ₐ[k'] L))
          = (galRes k K L) (AlgEquiv.restrictScalars k (σ : L ≃ₐ[k'] L)) from
        congrArg (fun (g : (L ≃ₐ[k'] L) →* (K ≃ₐ[k] K)) => g (σ : L ≃ₐ[k'] L))
          (galRes_restrictScalars k k' K L)])

theorem betaMap_apply (w : NK.GlobalCFT.Place K)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
    (f' : MulAction.stabilizer (L ≃ₐ[k'] L) w' →* decompK (k := k') w)
    (hf' : ∀ σ, ((f' σ : decompK (k := k') w) : K ≃ₐ[k'] K) = galRes k' K L (σ : L ≃ₐ[k'] L))
    (σ : MulAction.stabilizer (L ≃ₐ[k'] L) w') :
    ((betaMap (k := k) (k' := k') (K := K) (L := L) (w' := w') (w := w) (f := f) (hf := hf) (f' := f') (hf' := hf') σ :
        (baseChangeSubgroup k k' K w).comap f) : MulAction.stabilizer (L ≃ₐ[k] L) w')
      = thetaLMap k k' L w' σ := rfl

/-- `betaMap` is bijective. -/
theorem betaMap_bijective (w : NK.GlobalCFT.Place K)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
    (f' : MulAction.stabilizer (L ≃ₐ[k'] L) w' →* decompK (k := k') w)
    (hf' : ∀ σ, ((f' σ : decompK (k := k') w) : K ≃ₐ[k'] K) = galRes k' K L (σ : L ≃ₐ[k'] L)) :
    Function.Bijective (betaMap (k := k) (k' := k') (K := K) (L := L) (w' := w') (w := w)
      (f := f) (hf := hf) (f' := f') (hf' := hf')) := by
  constructor
  · intro σ τ hστ
    have h1 : (thetaLMap k k' L w' σ : L ≃ₐ[k] L) = (thetaLMap k k' L w' τ : L ≃ₐ[k] L) :=
      congrArg (fun x => (x.1 : L ≃ₐ[k] L)) hστ
    rw [thetaLMap_apply, thetaLMap_apply] at h1
    exact Subtype.ext (AlgEquiv.restrictScalars_injective k h1)
  · intro τ
    let σ₀ : L ≃ₐ[k] L := (τ.1 : MulAction.stabilizer (L ≃ₐ[k] L) w')
    have hτmem : f (τ.1 : MulAction.stabilizer (L ≃ₐ[k] L) w') ∈ baseChangeSubgroup k k' K w :=
      τ.2
    simp only [baseChangeSubgroup] at hτmem
    rw [Subgroup.mem_comap, Subgroup.mem_map] at hτmem
    obtain ⟨κ, _hκ, hθκ⟩ := hτmem
    have hgal : galRes k K L σ₀ = AlgEquiv.restrictScalars k κ := by
      have h := hf (τ.1 : MulAction.stabilizer (L ≃ₐ[k] L) w')
      rw [← h]
      rw [show AlgEquiv.restrictScalars k κ
          = (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K)) κ from rfl]
      exact hθκ.symm
    have hfix : ∀ c : k', σ₀ (algebraMap k' L c) = algebraMap k' L c := by
      intro c
      have h2 := (AlgEquiv.restrictNormal_commutes σ₀ K (algebraMap k' K c)).symm
      calc σ₀ (algebraMap k' L c)
          = σ₀ (algebraMap K L (algebraMap k' K c)) := by
            rw [IsScalarTower.algebraMap_apply k' K L]
        _ = algebraMap K L ((galRes k K L σ₀) (algebraMap k' K c)) := h2
        _ = algebraMap K L ((AlgEquiv.restrictScalars k κ) (algebraMap k' K c)) := by rw [hgal]
        _ = algebraMap K L (κ (algebraMap k' K c)) := rfl
        _ = algebraMap K L (algebraMap k' K c) := by
              rw [AlgEquiv.commutes κ c]
        _ = algebraMap k' L c := (IsScalarTower.algebraMap_apply k' K L c).symm
    let σ' : L ≃ₐ[k'] L := AlgEquiv.ofRingEquiv (f := (σ₀ : L ≃ₐ[k] L).toRingEquiv) hfix
    have hσ'restrict : AlgEquiv.restrictScalars k σ' = (σ₀ : L ≃ₐ[k] L) := by
      apply AlgEquiv.ext; intro x; rfl
    refine ⟨⟨σ', ?_⟩, ?_⟩
    · rw [MulAction.mem_stabilizer_iff]
      show σ' • w' = w'
      rw [← restrictScalars_smul_place_L k k' L w' σ', hσ'restrict]
      exact MulAction.mem_stabilizer_iff.mp τ.1.2
    · apply Subtype.ext
      apply Subtype.ext
      show (thetaLMap k k' L w' ⟨σ', _⟩ : L ≃ₐ[k] L) = σ₀
      rw [thetaLMap_apply]
      exact hσ'restrict

noncomputable def levelEquiv (w : NK.GlobalCFT.Place K)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
    (f' : MulAction.stabilizer (L ≃ₐ[k'] L) w' →* decompK (k := k') w)
    (hf' : ∀ σ, ((f' σ : decompK (k := k') w) : K ≃ₐ[k'] K) = galRes k' K L (σ : L ≃ₐ[k'] L)) :
    MulAction.stabilizer (L ≃ₐ[k'] L) w' ≃* (baseChangeSubgroup k k' K w).comap f :=
  MulEquiv.ofBijective _ (betaMap_bijective (k := k) (k' := k') (K := K) (L := L) (w' := w') (w := w) (f := f) (hf := hf) (f' := f') (hf' := hf'))

theorem levelEquiv_apply (w : NK.GlobalCFT.Place K)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
    (f' : MulAction.stabilizer (L ≃ₐ[k'] L) w' →* decompK (k := k') w)
    (hf' : ∀ σ, ((f' σ : decompK (k := k') w) : K ≃ₐ[k'] K) = galRes k' K L (σ : L ≃ₐ[k'] L))
    (σ : MulAction.stabilizer (L ≃ₐ[k'] L) w') :
    ((levelEquiv k k' K L w' w f hf f' hf' σ :
        (baseChangeSubgroup k k' K w).comap f) : MulAction.stabilizer (L ≃ₐ[k] L) w')
      = thetaLMap k k' L w' σ := rfl

theorem levelEquiv_f_apply (w : NK.GlobalCFT.Place K)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
    (f' : MulAction.stabilizer (L ≃ₐ[k'] L) w' →* decompK (k := k') w)
    (hf' : ∀ σ, ((f' σ : decompK (k := k') w) : K ≃ₐ[k'] K) = galRes k' K L (σ : L ≃ₐ[k'] L))
    (σ : MulAction.stabilizer (L ≃ₐ[k'] L) w') :
    (f (levelEquiv k k' K L w' w f hf f' hf' σ) : decompK (k := k) w)
      = (f (thetaLMap k k' L w' σ) : decompK (k := k) w) := rfl

/-! ### Tests of the representation identities -/

example (w : NK.GlobalCFT.Place K) (M : Rep Coeff (K ≃ₐ[k] K)) :
    Rep.res (baseChangeMulEquiv k k' K w).toMonoidHom
        (Rep.res (baseChangeSubgroup k k' K w).subtype (Rep.res (decompK (k := k) w).subtype M))
      = Rep.res (decompK (k := k') w).subtype
          (Rep.res (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K)) M) := rfl

example (w : NK.GlobalCFT.Place K) :
    Rep.res (baseChangeMulEquiv k k' K w).toMonoidHom
        (Rep.res (baseChangeSubgroup k k' K w).subtype (localUnitsK (k := k) w))
      = localUnitsK (k := k') w := rfl

/-- The `M`-coefficient identification at a level (Y3), as the identity on carriers. -/
noncomputable def rep_res_levelEquiv_M (w : NK.GlobalCFT.Place K) (M : Rep Coeff (K ≃ₐ[k] K))
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
    (f' : MulAction.stabilizer (L ≃ₐ[k'] L) w' →* decompK (k := k') w)
    (hf' : ∀ σ, ((f' σ : decompK (k := k') w) : K ≃ₐ[k'] K) = galRes k' K L (σ : L ≃ₐ[k'] L)) :
    Rep.res (levelEquiv k k' K L w' w f hf f' hf').toMonoidHom
        (Rep.res (f.subgroupComap (baseChangeSubgroup k k' K w))
          (Rep.res (baseChangeSubgroup k k' K w).subtype
            (Rep.res (decompK (k := k) w).subtype M)))
      ≅ Rep.res f' (Rep.res (decompK (k := k') w).subtype
          (Rep.res (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K)) M)) where
  hom := Rep.ofHom ⟨LinearMap.id, fun σ => by
    ext x
    have h1 : (((f.subgroupComap (baseChangeSubgroup k k' K w))
        (levelEquiv k k' K L w' w f hf f' hf' σ) :
          decompK (k := k) w) : K ≃ₐ[k] K)
        = (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K))
            (((f' σ : decompK (k := k') w) : K ≃ₐ[k'] K)) := by
      show ((f (thetaLMap k k' L w' σ) : decompK (k := k) w) : K ≃ₐ[k] K)
          = (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K))
              (((f' σ : decompK (k := k') w) : K ≃ₐ[k'] K))
      rw [hf (thetaLMap k k' L w' σ)]
      rw [thetaLMap_apply]
      rw [hf' σ]
      rw [show (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K))
            ((galRes k' K L) (σ : L ≃ₐ[k'] L))
          = (galRes k K L) (AlgEquiv.restrictScalars k (σ : L ≃ₐ[k'] L)) from
        congrArg (fun (g : (L ≃ₐ[k'] L) →* (K ≃ₐ[k] K)) => g (σ : L ≃ₐ[k'] L))
          (galRes_restrictScalars k k' K L)]
    show M.ρ (((f.subgroupComap (baseChangeSubgroup k k' K w))
        (levelEquiv k k' K L w' w f hf f' hf' σ) :
          decompK (k := k) w) : K ≃ₐ[k] K) x
      = M.ρ ((AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K))
          (((f' σ : decompK (k := k') w) : K ≃ₐ[k'] K))) x
    rw [h1]⟩
  inv := Rep.ofHom ⟨LinearMap.id, fun σ => by
    ext x
    have h1 : (((f.subgroupComap (baseChangeSubgroup k k' K w))
        (levelEquiv k k' K L w' w f hf f' hf' σ) :
          decompK (k := k) w) : K ≃ₐ[k] K)
        = (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K))
            (((f' σ : decompK (k := k') w) : K ≃ₐ[k'] K)) := by
      show ((f (thetaLMap k k' L w' σ) : decompK (k := k) w) : K ≃ₐ[k] K)
          = (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K))
              (((f' σ : decompK (k := k') w) : K ≃ₐ[k'] K))
      rw [hf (thetaLMap k k' L w' σ)]
      rw [thetaLMap_apply]
      rw [hf' σ]
      rw [show (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K))
            ((galRes k' K L) (σ : L ≃ₐ[k'] L))
          = (galRes k K L) (AlgEquiv.restrictScalars k (σ : L ≃ₐ[k'] L)) from
        congrArg (fun (g : (L ≃ₐ[k'] L) →* (K ≃ₐ[k] K)) => g (σ : L ≃ₐ[k'] L))
          (galRes_restrictScalars k k' K L)]
    show M.ρ ((AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K))
          (((f' σ : decompK (k := k') w) : K ≃ₐ[k'] K))) x
      = M.ρ (((f.subgroupComap (baseChangeSubgroup k k' K w))
        (levelEquiv k k' K L w' w f hf f' hf' σ) :
          decompK (k := k) w) : K ≃ₐ[k] K) x
    rw [h1]⟩
  hom_inv_id := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    rfl
  inv_hom_id := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    rfl

/-- The local-units coefficient identification at a level (Y3). -/
noncomputable def rep_res_levelEquiv_localUnits (w : NK.GlobalCFT.Place K)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
    (f' : MulAction.stabilizer (L ≃ₐ[k'] L) w' →* decompK (k := k') w)
    (hf' : ∀ σ, ((f' σ : decompK (k := k') w) : K ≃ₐ[k'] K) = galRes k' K L (σ : L ≃ₐ[k'] L)) :
    Rep.res (levelEquiv k k' K L w' w f hf f' hf').toMonoidHom
        (Rep.res ((baseChangeSubgroup k k' K w).comap f).subtype
          (NK.HassePrinciple.localUnitsRep k L w'))
      ≅ NK.HassePrinciple.localUnitsRep k' L w' where
  hom := Rep.ofHom ⟨LinearMap.id, fun σ => by
    ext x
    rw [MonoidHom.comp_apply, Rep.res_obj_ρ, MonoidHom.comp_apply]
    rfl⟩
  inv := Rep.ofHom ⟨LinearMap.id, fun σ => by
    ext x
    rw [MonoidHom.comp_apply, Rep.res_obj_ρ, MonoidHom.comp_apply]
    rfl⟩
  hom_inv_id := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    rfl
  inv_hom_id := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    rfl

end Level

end Work.SSGRoute.Y3Dev
