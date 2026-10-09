import Mathlib
import Submission.Work.SSGRoute.E7bDefs
import Submission.Work.SSGRoute.decompK_restrict_exists
import Submission.Work.SSGRoute.localUnitsMap_exists
import Submission.Work.SSGRoute.ext_corestriction
import Submission.Work.SSGRoute.ext_res_mulEquiv
import Submission.Work.SSGRoute.nonempty_extH_addEquiv_mulEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END


open SSGRoute.PTExt CategoryTheory

set_option maxHeartbeats 3200000


set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.SSGRoute.Y3Test

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

noncomputable def thetaLMap (k k' L : Type) [Field k] [NumberField k] [Field k'] [NumberField k']
    [Field L] [NumberField L]
    [Algebra k L] [Algebra k' L] [Algebra k k'] [IsScalarTower k k' L]
    (w' : NK.GlobalCFT.Place L) :
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
      show ((AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K)).comp (galRes k' K L))
            (σ : L ≃ₐ[k'] L)
          = ((galRes k K L).comp (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := L)))
            (σ : L ≃ₐ[k'] L)
      rw [galRes_restrictScalars])

theorem betaMap_apply (w : NK.GlobalCFT.Place K)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
    (f' : MulAction.stabilizer (L ≃ₐ[k'] L) w' →* decompK (k := k') w)
    (hf' : ∀ σ, ((f' σ : decompK (k := k') w) : K ≃ₐ[k'] K) = galRes k' K L (σ : L ≃ₐ[k'] L))
    (σ : MulAction.stabilizer (L ≃ₐ[k'] L) w') :
    ((betaMap (k := k) (k' := k') (K := K) (L := L) (w' := w') (w := w) (f := f) (hf := hf)
        (f' := f') (hf' := hf') σ : (baseChangeSubgroup k k' K w).comap f)
        : MulAction.stabilizer (L ≃ₐ[k] L) w')
      = thetaLMap k k' L w' σ := rfl

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
  MulEquiv.ofBijective _ (betaMap_bijective k k' K L w' w f hf f' hf')

theorem levelEquiv_apply (w : NK.GlobalCFT.Place K)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
    (f' : MulAction.stabilizer (L ≃ₐ[k'] L) w' →* decompK (k := k') w)
    (hf' : ∀ σ, ((f' σ : decompK (k := k') w) : K ≃ₐ[k'] K) = galRes k' K L (σ : L ≃ₐ[k'] L))
    (σ : MulAction.stabilizer (L ≃ₐ[k'] L) w') :
    (f (levelEquiv k k' K L w' w f hf f' hf' σ) : decompK (k := k) w)
      = f (thetaLMap k k' L w' σ) := rfl

theorem levelEquiv_theta (w : NK.GlobalCFT.Place K)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
    (f' : MulAction.stabilizer (L ≃ₐ[k'] L) w' →* decompK (k := k') w)
    (hf' : ∀ σ, ((f' σ : decompK (k := k') w) : K ≃ₐ[k'] K) = galRes k' K L (σ : L ≃ₐ[k'] L))
    (σ : MulAction.stabilizer (L ≃ₐ[k'] L) w') :
    ((levelEquiv k k' K L w' w f hf f' hf' σ : (baseChangeSubgroup k k' K w).comap f)
        : MulAction.stabilizer (L ≃ₐ[k] L) w')
      = thetaLMap k k' L w' σ := rfl

/-- The homomorphism equation `f.subgroupComap S ∘ β = α ∘ f'`. -/
theorem hcomm_aux (w : NK.GlobalCFT.Place K)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
    (f' : MulAction.stabilizer (L ≃ₐ[k'] L) w' →* decompK (k := k') w)
    (hf' : ∀ σ, ((f' σ : decompK (k := k') w) : K ≃ₐ[k'] K) = galRes k' K L (σ : L ≃ₐ[k'] L)) :
    (f.subgroupComap (baseChangeSubgroup k k' K w)).comp
        (levelEquiv k k' K L w' w f hf f' hf').toMonoidHom
      = (baseChangeMulEquiv k k' K w).toMonoidHom.comp f' := by
  refine MonoidHom.ext fun σ => Subtype.ext ?_
  show (f (((levelEquiv k k' K L w' w f hf f' hf') σ) :
        MulAction.stabilizer (L ≃ₐ[k] L) w') : decompK (k := k) w)
      = (baseChangeMulEquiv k k' K w) (f' σ)
  rw [levelEquiv_theta k k' K L w' w f hf f' hf' σ]
  apply Subtype.ext
  show (↑(f ((thetaLMap k k' L w') σ)) : K ≃ₐ[k] K)
      = (↑((baseChangeMulEquiv k k' K w) (f' σ)) : K ≃ₐ[k] K)
  rw [hf (thetaLMap k k' L w' σ), thetaLMap_apply]
  rw [show (↑((baseChangeMulEquiv k k' K w) (f' σ)) : K ≃ₐ[k] K)
      = (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K))
          ((f' σ : decompK (k := k') w) : K ≃ₐ[k'] K) from rfl]
  rw [show (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K))
          ((f' σ : decompK (k := k') w) : K ≃ₐ[k'] K)
      = (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K))
          (galRes k' K L (σ : L ≃ₐ[k'] L)) from congrArg _ (hf' σ)]
  rw [show (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K))
          (galRes k' K L (σ : L ≃ₐ[k'] L))
      = ((AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K)).comp (galRes k' K L))
          (σ : L ≃ₐ[k'] L) from rfl]
  rw [← galRes_restrictScalars]
  rfl

/-- The representation identity `res_β XS = XS'`. -/
theorem res_beta_XS (w : NK.GlobalCFT.Place K)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
    (f' : MulAction.stabilizer (L ≃ₐ[k'] L) w' →* decompK (k := k') w)
    (hf' : ∀ σ, ((f' σ : decompK (k := k') w) : K ≃ₐ[k'] K) = galRes k' K L (σ : L ≃ₐ[k'] L))
    (M : Rep Coeff (K ≃ₐ[k] K)) :
    Rep.res (levelEquiv k k' K L w' w f hf f' hf').toMonoidHom
        (Rep.res (f.subgroupComap (baseChangeSubgroup k k' K w))
          (Rep.res (baseChangeSubgroup k k' K w).subtype (Rep.res (decompK (k := k) w).subtype M)))
      = Rep.res f' (Rep.res (decompK (k := k') w).subtype
          (Rep.res (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K)) M)) := by
  show Rep.res ((f.subgroupComap (baseChangeSubgroup k k' K w)).comp
        (levelEquiv k k' K L w' w f hf f' hf').toMonoidHom)
        (Rep.res (baseChangeSubgroup k k' K w).subtype (Rep.res (decompK (k := k) w).subtype M))
      = Rep.res f' (Rep.res (decompK (k := k') w).subtype
          (Rep.res (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K)) M))
  rw [hcomm_aux k k' K L w' w f hf f' hf']
  rfl

/-- The `ρ`-value of the level-`k` local units at the transported element. -/
theorem localUnits_rho_comp (w : NK.GlobalCFT.Place K)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
    (f' : MulAction.stabilizer (L ≃ₐ[k'] L) w' →* decompK (k := k') w)
    (hf' : ∀ σ, ((f' σ : decompK (k := k') w) : K ≃ₐ[k'] K) = galRes k' K L (σ : L ≃ₐ[k'] L))
    (σ : MulAction.stabilizer (L ≃ₐ[k'] L) w') :
    (NK.HassePrinciple.localUnitsRep k L w').ρ
        (((levelEquiv k k' K L w' w f hf f' hf') σ :
            (baseChangeSubgroup k k' K w).comap f) :
          MulAction.stabilizer (L ≃ₐ[k] L) w')
      = (NK.HassePrinciple.localUnitsRep k' L w').ρ σ := by
  rw [levelEquiv_theta k k' K L w' w f hf f' hf' σ]
  rfl

/-- The representation identity `res_β YS = YS'`. -/
theorem res_beta_YS (w : NK.GlobalCFT.Place K)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
    (f' : MulAction.stabilizer (L ≃ₐ[k'] L) w' →* decompK (k := k') w)
    (hf' : ∀ σ, ((f' σ : decompK (k := k') w) : K ≃ₐ[k'] K) = galRes k' K L (σ : L ≃ₐ[k'] L)) :
    Rep.res (levelEquiv k k' K L w' w f hf f' hf').toMonoidHom
        (Rep.res ((baseChangeSubgroup k k' K w).comap f).subtype
          (NK.HassePrinciple.localUnitsRep k L w'))
      = NK.HassePrinciple.localUnitsRep k' L w' := by
  show Rep.of (((NK.HassePrinciple.localUnitsRep k L w').ρ.comp
        ((baseChangeSubgroup k k' K w).comap f).subtype).comp
        (levelEquiv k k' K L w' w f hf f' hf').toMonoidHom)
      = Rep.of ((NK.HassePrinciple.localUnitsRep k' L w').ρ)
  rw [show ((NK.HassePrinciple.localUnitsRep k L w').ρ.comp
        ((baseChangeSubgroup k k' K w).comap f).subtype).comp
        (levelEquiv k k' K L w' w f hf f' hf').toMonoidHom
      = (NK.HassePrinciple.localUnitsRep k' L w').ρ from
    MonoidHom.ext fun σ => localUnits_rho_comp k k' K L w' w f hf f' hf' σ]
  rfl

end Level

/-! ## The three additive equivalences -/

noncomputable def eEdef (w : NK.GlobalCFT.Place K) (M : Rep Coeff (K ≃ₐ[k] K)) :
    Abelian.Ext (Rep.res (baseChangeSubgroup k k' K w).subtype
          (Rep.res (decompK (k := k) w).subtype M))
        (Rep.res (baseChangeSubgroup k k' K w).subtype (localUnitsK (k := k) w)) 1 ≃+
      Abelian.Ext (Rep.res (decompK (k := k') w).subtype
          (Rep.res (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K)) M))
        (localUnitsK (k := k') w) 1 := by
  haveI : (Rep.resFunctor (baseChangeMulEquiv k k' K w).toMonoidHom).IsEquivalence :=
    Work.SSGRoute.resFunctor_isEquivalence_toMonoidHom _
  exact AddEquiv.ofBijective
    ((Rep.resFunctor (baseChangeMulEquiv k k' K w).toMonoidHom).mapExtAddHom
      (Rep.res (baseChangeSubgroup k k' K w).subtype (Rep.res (decompK (k := k) w).subtype M))
      (Rep.res (baseChangeSubgroup k k' K w).subtype (localUnitsK (k := k) w)) 1)
    (Functor.mapExt_bijective_of_preservesProjectiveObjects _ _ _ _)

theorem eEdef_apply (w : NK.GlobalCFT.Place K) (M : Rep Coeff (K ≃ₐ[k] K))
    (z : Abelian.Ext (Rep.res (baseChangeSubgroup k k' K w).subtype
          (Rep.res (decompK (k := k) w).subtype M))
        (Rep.res (baseChangeSubgroup k k' K w).subtype (localUnitsK (k := k) w)) 1) :
    eEdef k k' K w M z
      = extRes (baseChangeMulEquiv k k' K w).toMonoidHom z := rfl

section Level2

variable (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [FiniteDimensional k L] [IsGalois k L] [Algebra k' L] [IsScalarTower k' K L]
  [IsScalarTower k k' L] [FiniteDimensional k' L] [IsGalois k' L]
  (w' : NK.GlobalCFT.Place L)

/-- Bijectivity of the `mk₀`-transport of `Ext`-cohomology. -/
theorem mk0_transport_bijective (w : NK.GlobalCFT.Place K) (M : Rep Coeff (K ≃ₐ[k] K))
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
    (f' : MulAction.stabilizer (L ≃ₐ[k'] L) w' →* decompK (k := k') w)
    (hf' : ∀ σ, ((f' σ : decompK (k := k') w) : K ≃ₐ[k'] K) = galRes k' K L (σ : L ≃ₐ[k'] L)) :
    Function.Bijective (fun t : extH (Rep.res (levelEquiv k k' K L w' w f hf f' hf').toMonoidHom
        (Rep.res (f.subgroupComap (baseChangeSubgroup k k' K w))
          (Rep.res (baseChangeSubgroup k k' K w).subtype (Rep.res (decompK (k := k) w).subtype M)))) 1 =>
      t.comp (Abelian.Ext.mk₀ (eqToIso (res_beta_XS k k' K L w' w f hf f' hf' M)).hom) (add_zero 1)) := by
  let iX := eqToIso (res_beta_XS k k' K L w' w f hf f' hf' M)
  refine ⟨fun a b hab => ?_, fun b => ⟨b.comp (Abelian.Ext.mk₀ iX.inv) (add_zero 1), ?_⟩⟩
  · have h2 : (a.comp (Abelian.Ext.mk₀ iX.hom) (add_zero 1)).comp (Abelian.Ext.mk₀ iX.inv) (add_zero 1) = a := by
      rw [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀, show iX.hom ≫ iX.inv = 𝟙 _ from iX.hom_inv_id,
        Abelian.Ext.comp_mk₀_id]
    have h3 : (b.comp (Abelian.Ext.mk₀ iX.hom) (add_zero 1)).comp (Abelian.Ext.mk₀ iX.inv) (add_zero 1) = b := by
      rw [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀, show iX.hom ≫ iX.inv = 𝟙 _ from iX.hom_inv_id,
        Abelian.Ext.comp_mk₀_id]
    have h := congrArg (fun t => t.comp (Abelian.Ext.mk₀ iX.inv) (add_zero 1)) hab
    simp only at h
    rw [h2, h3] at h
    exact h
  · show (b.comp (Abelian.Ext.mk₀ iX.inv) (add_zero 1)).comp (Abelian.Ext.mk₀ iX.hom) (add_zero 1) = b
    rw [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
      show iX.inv ≫ iX.hom = 𝟙 _ from iX.inv_hom_id, Abelian.Ext.comp_mk₀_id]

/-- Bijectivity of the `mk₀`-transport on `H²`. -/
theorem mk0_transport2_bijective (w : NK.GlobalCFT.Place K)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
    (f' : MulAction.stabilizer (L ≃ₐ[k'] L) w' →* decompK (k := k') w)
    (hf' : ∀ σ, ((f' σ : decompK (k := k') w) : K ≃ₐ[k'] K) = galRes k' K L (σ : L ≃ₐ[k'] L)) :
    Function.Bijective (fun t : extH (Rep.res (levelEquiv k k' K L w' w f hf f' hf').toMonoidHom
        (Rep.res ((baseChangeSubgroup k k' K w).comap f).subtype
          (NK.HassePrinciple.localUnitsRep k L w'))) 2 =>
      t.comp (Abelian.Ext.mk₀ (eqToIso (res_beta_YS k k' K L w' w f hf f' hf')).hom) (add_zero 2)) := by
  let iB := eqToIso (res_beta_YS k k' K L w' w f hf f' hf')
  refine ⟨fun a b hab => ?_, fun b => ⟨b.comp (Abelian.Ext.mk₀ iB.inv) (add_zero 2), ?_⟩⟩
  · have h2 : (a.comp (Abelian.Ext.mk₀ iB.hom) (add_zero 2)).comp (Abelian.Ext.mk₀ iB.inv) (add_zero 2) = a := by
      rw [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀, show iB.hom ≫ iB.inv = 𝟙 _ from iB.hom_inv_id,
        Abelian.Ext.comp_mk₀_id]
    have h3 : (b.comp (Abelian.Ext.mk₀ iB.hom) (add_zero 2)).comp (Abelian.Ext.mk₀ iB.inv) (add_zero 2) = b := by
      rw [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀, show iB.hom ≫ iB.inv = 𝟙 _ from iB.hom_inv_id,
        Abelian.Ext.comp_mk₀_id]
    have h := congrArg (fun t => t.comp (Abelian.Ext.mk₀ iB.inv) (add_zero 2)) hab
    simp only at h
    rw [h2, h3] at h
    exact h
  · show (b.comp (Abelian.Ext.mk₀ iB.inv) (add_zero 2)).comp (Abelian.Ext.mk₀ iB.hom) (add_zero 2) = b
    rw [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
      show iB.inv ≫ iB.hom = 𝟙 _ from iB.inv_hom_id, Abelian.Ext.comp_mk₀_id]

/-- The group-change bijectivity on `H¹`. -/
theorem groupChange_bijective (w : NK.GlobalCFT.Place K) (M : Rep Coeff (K ≃ₐ[k] K))
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
    (f' : MulAction.stabilizer (L ≃ₐ[k'] L) w' →* decompK (k := k') w)
    (hf' : ∀ σ, ((f' σ : decompK (k := k') w) : K ≃ₐ[k'] K) = galRes k' K L (σ : L ≃ₐ[k'] L)) :
    Function.Bijective (fun t : extH (Rep.res (f.subgroupComap (baseChangeSubgroup k k' K w))
        (Rep.res (baseChangeSubgroup k k' K w).subtype (Rep.res (decompK (k := k) w).subtype M))) 1 =>
      extRes (levelEquiv k k' K L w' w f hf f' hf').toMonoidHom t) := by
  haveI : (Rep.resFunctor (levelEquiv k k' K L w' w f hf f' hf').toMonoidHom).IsEquivalence :=
    Work.SSGRoute.resFunctor_isEquivalence_toMonoidHom _
  have h := Functor.mapExt_bijective_of_preservesProjectiveObjects
    (Rep.resFunctor (levelEquiv k k' K L w' w f hf f' hf').toMonoidHom)
    (unitRep ((baseChangeSubgroup k k' K w).comap f))
    (Rep.res (f.subgroupComap (baseChangeSubgroup k k' K w))
      (Rep.res (baseChangeSubgroup k k' K w).subtype (Rep.res (decompK (k := k) w).subtype M))) 1
  show Function.Bijective (fun t => ((Rep.resFunctor (levelEquiv k k' K L w' w f hf f' hf').toMonoidHom).mapExtAddHom _ _ 1) t)
  exact h

/-- The group-change bijectivity on `H²`. -/
theorem groupChange2_bijective (w : NK.GlobalCFT.Place K)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
    (f' : MulAction.stabilizer (L ≃ₐ[k'] L) w' →* decompK (k := k') w)
    (hf' : ∀ σ, ((f' σ : decompK (k := k') w) : K ≃ₐ[k'] K) = galRes k' K L (σ : L ≃ₐ[k'] L)) :
    Function.Bijective (fun t : extH (Rep.res ((baseChangeSubgroup k k' K w).comap f).subtype
        (NK.HassePrinciple.localUnitsRep k L w')) 2 =>
      extRes (levelEquiv k k' K L w' w f hf f' hf').toMonoidHom t) := by
  haveI : (Rep.resFunctor (levelEquiv k k' K L w' w f hf f' hf').toMonoidHom).IsEquivalence :=
    Work.SSGRoute.resFunctor_isEquivalence_toMonoidHom _
  have h := Functor.mapExt_bijective_of_preservesProjectiveObjects
    (Rep.resFunctor (levelEquiv k k' K L w' w f hf f' hf').toMonoidHom)
    (unitRep ((baseChangeSubgroup k k' K w).comap f))
    (Rep.res ((baseChangeSubgroup k k' K w).comap f).subtype
      (NK.HassePrinciple.localUnitsRep k L w')) 2
  show Function.Bijective (fun t => ((Rep.resFunctor (levelEquiv k k' K L w' w f hf f' hf').toMonoidHom).mapExtAddHom _ _ 2) t)
  exact h

/-- The `mk₀`-transport at a level (`H¹`). -/
noncomputable def mk0Equiv1 (w : NK.GlobalCFT.Place K) (M : Rep Coeff (K ≃ₐ[k] K))
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
    (f' : MulAction.stabilizer (L ≃ₐ[k'] L) w' →* decompK (k := k') w)
    (hf' : ∀ σ, ((f' σ : decompK (k := k') w) : K ≃ₐ[k'] K) = galRes k' K L (σ : L ≃ₐ[k'] L)) :
    extH (Rep.res (levelEquiv k k' K L w' w f hf f' hf').toMonoidHom
        (Rep.res (f.subgroupComap (baseChangeSubgroup k k' K w))
          (Rep.res (baseChangeSubgroup k k' K w).subtype (Rep.res (decompK (k := k) w).subtype M)))) 1 ≃+
      extH (Rep.res f' (Rep.res (decompK (k := k') w).subtype
        (Rep.res (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K)) M))) 1 where
  toFun t := t.comp (Abelian.Ext.mk₀
    (eqToIso (res_beta_XS k k' K L w' w f hf f' hf' M)).hom) (add_zero 1)
  invFun t := t.comp (Abelian.Ext.mk₀
    (eqToIso (res_beta_XS k k' K L w' w f hf f' hf' M)).inv) (add_zero 1)
  left_inv t := by
    show (t.comp (Abelian.Ext.mk₀ (eqToIso (res_beta_XS k k' K L w' w f hf f' hf' M)).hom) (add_zero 1)).comp
      (Abelian.Ext.mk₀ (eqToIso (res_beta_XS k k' K L w' w f hf f' hf' M)).inv) (add_zero 1) = t
    rw [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
      show (eqToIso (res_beta_XS k k' K L w' w f hf f' hf' M)).hom
          ≫ (eqToIso (res_beta_XS k k' K L w' w f hf f' hf' M)).inv = 𝟙 _ from
        (eqToIso (res_beta_XS k k' K L w' w f hf f' hf' M)).hom_inv_id,
      Abelian.Ext.comp_mk₀_id]
  right_inv t := by
    show (t.comp (Abelian.Ext.mk₀ (eqToIso (res_beta_XS k k' K L w' w f hf f' hf' M)).inv) (add_zero 1)).comp
      (Abelian.Ext.mk₀ (eqToIso (res_beta_XS k k' K L w' w f hf f' hf' M)).hom) (add_zero 1) = t
    rw [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
      show (eqToIso (res_beta_XS k k' K L w' w f hf f' hf' M)).inv
          ≫ (eqToIso (res_beta_XS k k' K L w' w f hf f' hf' M)).hom = 𝟙 _ from
        (eqToIso (res_beta_XS k k' K L w' w f hf f' hf' M)).inv_hom_id,
      Abelian.Ext.comp_mk₀_id]
  map_add' a b := by
    show (a + b).comp (Abelian.Ext.mk₀ (eqToIso (res_beta_XS k k' K L w' w f hf f' hf' M)).hom) (add_zero 1)
      = a.comp (Abelian.Ext.mk₀ (eqToIso (res_beta_XS k k' K L w' w f hf f' hf' M)).hom) (add_zero 1)
        + b.comp (Abelian.Ext.mk₀ (eqToIso (res_beta_XS k k' K L w' w f hf f' hf' M)).hom) (add_zero 1)
    rw [Abelian.Ext.add_comp]

/-- The `mk₀`-transport at a level (`H²`). -/
noncomputable def mk0Equiv2 (w : NK.GlobalCFT.Place K)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
    (f' : MulAction.stabilizer (L ≃ₐ[k'] L) w' →* decompK (k := k') w)
    (hf' : ∀ σ, ((f' σ : decompK (k := k') w) : K ≃ₐ[k'] K) = galRes k' K L (σ : L ≃ₐ[k'] L)) :
    extH (Rep.res (levelEquiv k k' K L w' w f hf f' hf').toMonoidHom
        (Rep.res ((baseChangeSubgroup k k' K w).comap f).subtype
          (NK.HassePrinciple.localUnitsRep k L w'))) 2 ≃+
      extH (NK.HassePrinciple.localUnitsRep k' L w') 2 where
  toFun t := t.comp (Abelian.Ext.mk₀
    (eqToIso (res_beta_YS k k' K L w' w f hf f' hf')).hom) (add_zero 2)
  invFun t := t.comp (Abelian.Ext.mk₀
    (eqToIso (res_beta_YS k k' K L w' w f hf f' hf')).inv) (add_zero 2)
  left_inv t := by
    show (t.comp (Abelian.Ext.mk₀ (eqToIso (res_beta_YS k k' K L w' w f hf f' hf')).hom) (add_zero 2)).comp
      (Abelian.Ext.mk₀ (eqToIso (res_beta_YS k k' K L w' w f hf f' hf')).inv) (add_zero 2) = t
    rw [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
      show (eqToIso (res_beta_YS k k' K L w' w f hf f' hf')).hom
          ≫ (eqToIso (res_beta_YS k k' K L w' w f hf f' hf')).inv = 𝟙 _ from
        (eqToIso (res_beta_YS k k' K L w' w f hf f' hf')).hom_inv_id,
      Abelian.Ext.comp_mk₀_id]
  right_inv t := by
    show (t.comp (Abelian.Ext.mk₀ (eqToIso (res_beta_YS k k' K L w' w f hf f' hf')).inv) (add_zero 2)).comp
      (Abelian.Ext.mk₀ (eqToIso (res_beta_YS k k' K L w' w f hf f' hf')).hom) (add_zero 2) = t
    rw [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
      show (eqToIso (res_beta_YS k k' K L w' w f hf f' hf')).inv
          ≫ (eqToIso (res_beta_YS k k' K L w' w f hf f' hf')).hom = 𝟙 _ from
        (eqToIso (res_beta_YS k k' K L w' w f hf f' hf')).inv_hom_id,
      Abelian.Ext.comp_mk₀_id]
  map_add' a b := by
    show (a + b).comp (Abelian.Ext.mk₀ (eqToIso (res_beta_YS k k' K L w' w f hf f' hf')).hom) (add_zero 2)
      = a.comp (Abelian.Ext.mk₀ (eqToIso (res_beta_YS k k' K L w' w f hf f' hf')).hom) (add_zero 2)
        + b.comp (Abelian.Ext.mk₀ (eqToIso (res_beta_YS k k' K L w' w f hf f' hf')).hom) (add_zero 2)
    rw [Abelian.Ext.add_comp]

/-- The `Ext¹`-equivalence at a level. -/
noncomputable def eHdef (w : NK.GlobalCFT.Place K) (M : Rep Coeff (K ≃ₐ[k] K))
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
    (f' : MulAction.stabilizer (L ≃ₐ[k'] L) w' →* decompK (k := k') w)
    (hf' : ∀ σ, ((f' σ : decompK (k := k') w) : K ≃ₐ[k'] K) = galRes k' K L (σ : L ≃ₐ[k'] L)) :
    extH (Rep.res (f.subgroupComap (baseChangeSubgroup k k' K w))
        (Rep.res (baseChangeSubgroup k k' K w).subtype (Rep.res (decompK (k := k) w).subtype M))) 1 ≃+
      extH (Rep.res f' (Rep.res (decompK (k := k') w).subtype
        (Rep.res (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K)) M))) 1 :=
  (AddEquiv.ofBijective
    ((Rep.resFunctor (levelEquiv k k' K L w' w f hf f' hf').toMonoidHom).mapExtAddHom
      (unitRep ((baseChangeSubgroup k k' K w).comap f))
      (Rep.res (f.subgroupComap (baseChangeSubgroup k k' K w))
        (Rep.res (baseChangeSubgroup k k' K w).subtype (Rep.res (decompK (k := k) w).subtype M))) 1)
    (show Function.Bijective (fun t : extH (Rep.res (f.subgroupComap (baseChangeSubgroup k k' K w))
        (Rep.res (baseChangeSubgroup k k' K w).subtype (Rep.res (decompK (k := k) w).subtype M))) 1 =>
        (Rep.resFunctor (levelEquiv k k' K L w' w f hf f' hf').toMonoidHom).mapExtAddHom _ _ 1 t)
      from groupChange_bijective k k' K L w' w M f hf f' hf')).trans
    (AddEquiv.ofBijective (mk0Equiv1 k k' K L w' w M f hf f' hf')
      (show Function.Bijective (fun t : extH (Rep.res (levelEquiv k k' K L w' w f hf f' hf').toMonoidHom
          (Rep.res (f.subgroupComap (baseChangeSubgroup k k' K w))
            (Rep.res (baseChangeSubgroup k k' K w).subtype (Rep.res (decompK (k := k) w).subtype M)))) 1 =>
          t.comp (Abelian.Ext.mk₀ (eqToIso (res_beta_XS k k' K L w' w f hf f' hf' M)).hom) (add_zero 1))
        from mk0_transport_bijective k k' K L w' w M f hf f' hf'))

theorem eHdef_apply (w : NK.GlobalCFT.Place K) (M : Rep Coeff (K ≃ₐ[k] K))
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
    (f' : MulAction.stabilizer (L ≃ₐ[k'] L) w' →* decompK (k := k') w)
    (hf' : ∀ σ, ((f' σ : decompK (k := k') w) : K ≃ₐ[k'] K) = galRes k' K L (σ : L ≃ₐ[k'] L))
    (h : extH (Rep.res (f.subgroupComap (baseChangeSubgroup k k' K w))
        (Rep.res (baseChangeSubgroup k k' K w).subtype (Rep.res (decompK (k := k) w).subtype M))) 1) :
    eHdef k k' K L w' w M f hf f' hf' h
      = (extRes (levelEquiv k k' K L w' w f hf f' hf').toMonoidHom h).comp
          (Abelian.Ext.mk₀ (eqToIso (res_beta_XS k k' K L w' w f hf f' hf' M)).hom) (add_zero 1) :=
  rfl

/-- The `H²`-equivalence at a level. -/
noncomputable def eBdef (w : NK.GlobalCFT.Place K)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
    (f' : MulAction.stabilizer (L ≃ₐ[k'] L) w' →* decompK (k := k') w)
    (hf' : ∀ σ, ((f' σ : decompK (k := k') w) : K ≃ₐ[k'] K) = galRes k' K L (σ : L ≃ₐ[k'] L)) :
    extH (Rep.res ((baseChangeSubgroup k k' K w).comap f).subtype
        (NK.HassePrinciple.localUnitsRep k L w')) 2 ≃+
      extH (NK.HassePrinciple.localUnitsRep k' L w') 2 :=
  (AddEquiv.ofBijective
    ((Rep.resFunctor (levelEquiv k k' K L w' w f hf f' hf').toMonoidHom).mapExtAddHom
      (unitRep ((baseChangeSubgroup k k' K w).comap f))
      (Rep.res ((baseChangeSubgroup k k' K w).comap f).subtype
        (NK.HassePrinciple.localUnitsRep k L w')) 2)
    (show Function.Bijective (fun t : extH (Rep.res ((baseChangeSubgroup k k' K w).comap f).subtype
        (NK.HassePrinciple.localUnitsRep k L w')) 2 =>
        (Rep.resFunctor (levelEquiv k k' K L w' w f hf f' hf').toMonoidHom).mapExtAddHom _ _ 2 t)
      from groupChange2_bijective k k' K L w' w f hf f' hf')).trans
    (AddEquiv.ofBijective (mk0Equiv2 k k' K L w' w f hf f' hf')
      (show Function.Bijective (fun t : extH (Rep.res (levelEquiv k k' K L w' w f hf f' hf').toMonoidHom
          (Rep.res ((baseChangeSubgroup k k' K w).comap f).subtype
            (NK.HassePrinciple.localUnitsRep k L w'))) 2 =>
          t.comp (Abelian.Ext.mk₀ (eqToIso (res_beta_YS k k' K L w' w f hf f' hf')).hom) (add_zero 2))
        from mk0_transport2_bijective k k' K L w' w f hf f' hf'))

theorem eBdef_apply (w : NK.GlobalCFT.Place K)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
    (f' : MulAction.stabilizer (L ≃ₐ[k'] L) w' →* decompK (k := k') w)
    (hf' : ∀ σ, ((f' σ : decompK (k := k') w) : K ≃ₐ[k'] K) = galRes k' K L (σ : L ≃ₐ[k'] L))
    (t : extH (Rep.res ((baseChangeSubgroup k k' K w).comap f).subtype
        (NK.HassePrinciple.localUnitsRep k L w')) 2) :
    eBdef k k' K L w' w f hf f' hf' t
      = (extRes (levelEquiv k k' K L w' w f hf f' hf').toMonoidHom t).comp
          (Abelian.Ext.mk₀ (eqToIso (res_beta_YS k k' K L w' w f hf f' hf')).hom) (add_zero 2) :=
  rfl

end Level2


end Work.SSGRoute.Y3Test

namespace Work.SSGRoute.Y3Test

/-! ## Generic transport lemmas -/

theorem mk0_eqToHom_comp {G : Type} [Group G] {X Y Z : Rep Coeff G} {n : ℕ} (h : X = Y)
    (t : Abelian.Ext Y Z n) :
    (Abelian.Ext.mk₀ (eqToHom h)).comp t (zero_add n) = h.symm ▸ t := by
  cases h; simp

theorem comp_mk0_eqToHom {G : Type} [Group G] {X Y Z : Rep Coeff G} {n : ℕ} (h : X = Y)
    (t : Abelian.Ext Z X n) :
    t.comp (Abelian.Ext.mk₀ (eqToHom h)) (add_zero n) = h ▸ t := by
  cases h; simp

theorem mk0_transport_extRes {G H : Type} [Group G] [Group H] {M A : Rep Coeff G} {n : ℕ}
    (z : Abelian.Ext M A n) {g₁ g₂ : H →* G} (h : g₁ = g₂) :
    (Abelian.Ext.mk₀ (eqToHom (congrArg (fun g => Rep.res g M) h))).comp (extRes g₂ z) (zero_add n)
      = (congrArg (fun g => Rep.res g A) h) ▸ (extRes g₁ z) := by
  cases h; simp

theorem eqToHom_hom_id {G : Type} [Group G] {X Y : Rep Coeff G} (h : X = Y) (x : X.V) :
    (eqToHom h).hom x = h ▸ x := by
  cases h; rfl

end Work.SSGRoute.Y3Test


namespace Work.SSGRoute.Y3Test

theorem eqRec_eq_congrArg {G : Type} [Group G] {X Y : Rep Coeff G} (h : X = Y) (x : X.V) :
    (h ▸ x : Y.V) = (congrArg Rep.V h) ▸ x := by
  cases h; rfl

theorem eqRec_V_self {G : Type} [Group G] {X Y : Rep Coeff G} (h : X = Y) (x : X.V)
    (hV : X.V = Y.V) (hhV : congrArg Rep.V h = hV) : (h ▸ x : Y.V) = hV ▸ x := by
  rw [eqRec_eq_congrArg, hhV]

end Work.SSGRoute.Y3Test

namespace Work.SSGRoute.Y3Test

theorem eqToHom_hom_eq_cast {G : Type} [Group G] {X Y : Rep Coeff G} (h : X = Y) (x : X.V) :
    (Rep.Hom.hom (eqToHom h)) x = h ▸ x := by
  cases h; rfl

theorem eqToHom_hom_eq_self {G : Type} [Group G] {X Y : Rep Coeff G} (h : X = Y) (x : X.V)
    (hV : X.V = Y.V) (hhV : congrArg Rep.V h = hV) : (Rep.Hom.hom (eqToHom h)) x = hV ▸ x := by
  rw [eqToHom_hom_eq_cast]
  exact eqRec_V_self h x hV hhV

end Work.SSGRoute.Y3Test
