import Mathlib
import Submission.Work.SSGRoute.ArchDictionary.archPhiP2
import Submission.Work.SSGRoute.ArchDictionary.extOneDictNaturalH1
import Submission.Work.SSGRoute.ArchDictionary.p2Link
import Submission.Work.SSGRoute.ArchDictionary.archAcH1Natural
import Submission.Work.SSGRoute.ArchDictionary.placeLocalFieldComplex
import Submission.Work.SSGRoute.E1aClean.globalDictionaryCanonDefs
import Submission.Work.SSGRoute.ArchDictionary.archSeamDefs
import Submission.Work.SSGRoute.ArchDictionary.mapH1_coeff_comp
import Submission.Work.SSGRoute.ArchDictionary.eOf_symm_natural
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

Lead design archp2_1008. READ Submission/_lead_design/archp2_1008/ARCHP2_PLAN.md (and .lean). The old localCoeffP2/archPhiDef route can NEVER satisfy the comparison square: see the D₄ model in ARCHP2_model.lean (decide). This route uses Φ := ArchSeamP2.archPhiOf and Ψ := seamCoeffLoc (the seam-push of e1aCoeffNat), from the installed module Submission.Work.SSGRoute.ArchDictionary.archSeamDefs. The statement is lead-checked and elaborates. Copy any helper you need from the plan .lean; do not import _lead_design. No native_decide; never write maxHeartbeats 0.
-/

namespace Work.SSGRoute.ArchDictionary

open CategoryTheory CategoryTheory.Limits SSGRoute.PTExt Work.SSGRoute.ArchDictionary
  Work.SSGRoute.ArchDictionary.ArchSeamP2

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 8000000

/-- The computation rule of `ArchSeamP2.archPhiOf`. -/
theorem archPhiOf_apply {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    {T : Type} [AddCommGroup T] [Module (ZMod 2) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) T]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x)) (w : NK.GlobalCFT.Place ↥K)
    (hw : w = NK.GlobalCFT.Place.ofInfinite
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hne : decompK (k := k) w ≠ ⊥)
    (E : Type) [AddCommGroup E] [Module (ZMod 2) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) E] [Finite E]
    (M : Rep.{0} Coeff ↥(decompK (k := k) w))
    (Ψ : E ≃+ (M.V →ₗ[Coeff] (localUnitsK (k := k) w).V))
    (hΦ : @Work.GroupCohomology.IsEquivariant ↥(decompK (k := k) w) E
      (M.V →ₗ[Coeff] (localUnitsK (k := k) w).V) _ _ _ (dcAct K E w)
      (Work.SSGRoute.homRepDistribMulAction M (localUnitsK (k := k) w)) Ψ.toAddMonoidHom)
    (hΨ : @Work.GroupCohomology.IsEquivariant ↥(decompK (k := k) w)
      (M.V →ₗ[Coeff] (localUnitsK (k := k) w).V) E _ _ _
      (Work.SSGRoute.homRepDistribMulAction M (localUnitsK (k := k) w)) (dcAct K E w)
      Ψ.symm.toAddMonoidHom)
    (x : Ac (K := K) (E := E) c) :
    archPhiOf c hc2 hc1 φ hlink w hw hne E M Ψ hΦ hΨ x =
      (NatH1.eOf (N := localUnitsK (k := k) w)
        (moduleInjective_coeff_of_divisible _
          (show ∀ (n : ℕ), 0 < n → ∀ y : (localUnitsK (k := k) w).V,
            ∃ x : (localUnitsK (k := k) w).V, n • x = y from
            localUnitsK_divisible_of_decompK_ne_bot (k := k) (Ω := Ω) (K := K) φ w hw hne))
        (fun M => Classical.choose (homRepFree_coind_iso _ M.V _))
        (fun M => Classical.choose_spec (homRepFree_coind_iso _ M.V _)) M).symm
        (@Work.GroupCohomology.mapH1 ↥(decompK (k := k) w) E
          (M.V →ₗ[Coeff] (localUnitsK (k := k) w).V) _ _ _ (dcAct K E w)
          (Work.SSGRoute.homRepDistribMulAction M (localUnitsK (k := k) w))
          Ψ.toAddMonoidHom hΦ
          (cycTransfer (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink w hw hne E
            (acH1Equiv K c E x))) := rfl

theorem archPhiOf_natural {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (T : Type) [AddCommGroup T] [Module (ZMod 2) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) T]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x)) (w : NK.GlobalCFT.Place ↥K)
    (hw : w = NK.GlobalCFT.Place.ofInfinite
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hne : decompK (k := k) w ≠ ⊥)
    (E : Type) [AddCommGroup E] [Module (ZMod 2) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) E] [Finite E]
    (E₂ : Type) [AddCommGroup E₂] [Module (ZMod 2) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) E₂] [Finite E₂]
    (Ψ : E ≃+ ((Eprime 2 k Ω K T E).V →ₗ[Coeff] (localUnitsK (k := k) w).V))
    (hΦ : @Work.GroupCohomology.IsEquivariant ↥(decompK (k := k) w) E
      ((Eprime 2 k Ω K T E).V →ₗ[Coeff] (localUnitsK (k := k) w).V) _ _ _ (dcAct K E w)
      (Work.SSGRoute.homRepDistribMulAction
        (Rep.res (decompK (k := k) w).subtype (Eprime 2 k Ω K T E)) (localUnitsK (k := k) w))
      Ψ.toAddMonoidHom)
    (hΨ : @Work.GroupCohomology.IsEquivariant ↥(decompK (k := k) w)
      ((Eprime 2 k Ω K T E).V →ₗ[Coeff] (localUnitsK (k := k) w).V) E _ _ _
      (Work.SSGRoute.homRepDistribMulAction
        (Rep.res (decompK (k := k) w).subtype (Eprime 2 k Ω K T E)) (localUnitsK (k := k) w))
      (dcAct K E w) Ψ.symm.toAddMonoidHom)
    (Ψ₂ : E₂ ≃+ ((Eprime 2 k Ω K T E₂).V →ₗ[Coeff] (localUnitsK (k := k) w).V))
    (hΦ₂ : @Work.GroupCohomology.IsEquivariant ↥(decompK (k := k) w) E₂
      ((Eprime 2 k Ω K T E₂).V →ₗ[Coeff] (localUnitsK (k := k) w).V) _ _ _ (dcAct K E₂ w)
      (Work.SSGRoute.homRepDistribMulAction
        (Rep.res (decompK (k := k) w).subtype (Eprime 2 k Ω K T E₂)) (localUnitsK (k := k) w))
      Ψ₂.toAddMonoidHom)
    (hΨ₂ : @Work.GroupCohomology.IsEquivariant ↥(decompK (k := k) w)
      ((Eprime 2 k Ω K T E₂).V →ₗ[Coeff] (localUnitsK (k := k) w).V) E₂ _ _ _
      (Work.SSGRoute.homRepDistribMulAction
        (Rep.res (decompK (k := k) w).subtype (Eprime 2 k Ω K T E₂)) (localUnitsK (k := k) w))
      (dcAct K E₂ w) Ψ₂.symm.toAddMonoidHom)
    (f : E →ₗ[ZMod 2] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e)
    (F' : Eprime 2 k Ω K T E₂ ⟶ Eprime 2 k Ω K T E)
    (hnat : ∀ (e : E) (m : (Eprime 2 k Ω K T E₂).V), Ψ₂ (f e) m = Ψ e (F'.hom m))
    (x : Ac (K := K) (E := E) c) :
    archPhiOf c hc2 hc1 φ hlink w hw hne E₂
        (Rep.res (decompK (k := k) w).subtype (Eprime 2 k Ω K T E₂)) Ψ₂ hΦ₂ hΨ₂
        (Work.SSGRoute.ArchNat.AcMap (f : E →+ E₂) (fun g e => hf g e) c x)
      = (Abelian.Ext.mk₀ (Rep.resMap (decompK (k := k) w).subtype F')).comp
          (archPhiOf c hc2 hc1 φ hlink w hw hne E
            (Rep.res (decompK (k := k) w).subtype (Eprime 2 k Ω K T E)) Ψ hΦ hΨ x) (zero_add 1) := by
  classical
  have hA := archPhiOf_apply (k := k) (Ω := Ω) (K := K) (T := T) (c := c) (hc2 := hc2) (hc1 := hc1) (φ := φ) (hlink := hlink)
    (w := w) (hw := hw) (hne := hne) (E := E₂)
    (M := Rep.res (decompK (k := k) w).subtype (Eprime 2 k Ω K T E₂)) (Ψ := Ψ₂)
    (hΦ := hΦ₂) (hΨ := hΨ₂)
    (x := Work.SSGRoute.ArchNat.AcMap (f : E →+ E₂) (fun g e => hf g e) c x)
  have hB := archPhiOf_apply (k := k) (Ω := Ω) (K := K) (T := T) (c := c) (hc2 := hc2) (hc1 := hc1) (φ := φ) (hlink := hlink)
    (w := w) (hw := hw) (hne := hne) (E := E)
    (M := Rep.res (decompK (k := k) w).subtype (Eprime 2 k Ω K T E)) (Ψ := Ψ)
    (hΦ := hΦ) (hΨ := hΨ) (x := x)
  rw [hA, hB]
  rw [AddEquiv.symm_apply_eq]
  rw [eOf_symm_natural (N := localUnitsK (k := k) w)
    (hInj := moduleInjective_coeff_of_divisible _
      (show ∀ (n : ℕ), 0 < n → ∀ y : (localUnitsK (k := k) w).V,
        ∃ x : (localUnitsK (k := k) w).V, n • x = y from
        localUnitsK_divisible_of_decompK_ne_bot (k := k) (Ω := Ω) (K := K) φ w hw hne))
    (X := fun M => Classical.choose (Work.SSGRoute.homRepFree_coind_iso _ M.V _))
    (hX := fun M => Classical.choose_spec (Work.SSGRoute.homRepFree_coind_iso _ M.V _))
    (M' := Rep.res (decompK (k := k) w).subtype (Eprime 2 k Ω K T E₂))
    (M := Rep.res (decompK (k := k) w).subtype (Eprime 2 k Ω K T E))
    (u := Rep.resMap (decompK (k := k) w).subtype F')
    (y := @Work.GroupCohomology.mapH1 ↥(decompK (k := k) w) E
      ((Eprime 2 k Ω K T E).V →ₗ[Coeff] (localUnitsK (k := k) w).V) _ _ _
      (dcAct K E w)
      (Work.SSGRoute.homRepDistribMulAction
        (Rep.res (decompK (k := k) w).subtype (Eprime 2 k Ω K T E)) (localUnitsK (k := k) w))
      Ψ.toAddMonoidHom hΦ
      (Work.SSGRoute.ArchDictionary.cycTransfer (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink w hw
        hne E (Work.SSGRoute.ArchDictionary.acH1Equiv K c E x)))]
  letI hE1 : DistribMulAction ↥(decompK (k := k) w) E := dcAct K E w
  letI hE2 : DistribMulAction ↥(decompK (k := k) w) E₂ := dcAct K E₂ w
  have hf_cyc : @Work.GroupCohomology.IsEquivariant ↥(Subgroup.zpowers c) E E₂ _ _ _
      (cycAct K c E) (cycAct K c E₂) (f : E →+ E₂) :=
    fun g e => hf (SSGRoute.res k K (g : Ω ≃ₐ[k] Ω)) e
  have hf_D : @Work.GroupCohomology.IsEquivariant ↥(decompK (k := k) w) E E₂ _ _ _
      (dcAct K E w) (dcAct K E₂ w) (f : E →+ E₂) := fun g e => hf (g : K ≃ₐ[k] K) e
  have s1 := Work.SSGRoute.ArchDictionary.acH1Equiv_natural K c E E₂ (f : E →+ E₂)
    (fun g e => hf g e) hf_cyc x
  have s2 := Work.SSGRoute.ArchDictionary.cycTransfer_natural (k := k) (Ω := Ω) (K := K) c hc2
    hc1 φ hlink w hw hne E E₂ (f : E →+ E₂) hf_cyc hf_D (Work.SSGRoute.ArchDictionary.acH1Equiv K c E x)
  have hpp_apply : ∀ (ψ : (Rep.res (decompK (k := k) w).subtype (Eprime 2 k Ω K T E)).V
        →ₗ[Coeff] (localUnitsK (k := k) w).V) (m : (Eprime 2 k Ω K T E₂).V),
      (show (Rep.res (decompK (k := k) w).subtype (Eprime 2 k Ω K T E₂)).V
          →ₗ[Coeff] (localUnitsK (k := k) w).V from
        (Work.SSGRoute.homRepPre (Rep.res (decompK (k := k) w).subtype (Eprime 2 k Ω K T E))
          (Rep.res (decompK (k := k) w).subtype (Eprime 2 k Ω K T E₂))
          (localUnitsK (k := k) w) (Rep.resMap (decompK (k := k) w).subtype F')).hom ψ) m
        = ψ (F'.hom m) := by
    intro ψ m
    exact Work.SSGRoute.homRepPre_apply
      (Rep.res (decompK (k := k) w).subtype (Eprime 2 k Ω K T E))
      (Rep.res (decompK (k := k) w).subtype (Eprime 2 k Ω K T E₂))
      (localUnitsK (k := k) w) (Rep.resMap (decompK (k := k) w).subtype F') ψ m
  have hEq : Ψ₂.toAddMonoidHom.comp (f : E →+ E₂)
      = ((Work.SSGRoute.homRepPre (Rep.res (decompK (k := k) w).subtype (Eprime 2 k Ω K T E))
          (Rep.res (decompK (k := k) w).subtype (Eprime 2 k Ω K T E₂))
          (localUnitsK (k := k) w) (Rep.resMap (decompK (k := k) w).subtype F')).hom.toAddMonoidHom).comp
        Ψ.toAddMonoidHom := by
    refine AddMonoidHom.ext (fun e => ?_)
    refine LinearMap.ext (fun m => ?_)
    show (Ψ₂ ((f : E →+ E₂) e)) m
      = (show (Rep.res (decompK (k := k) w).subtype (Eprime 2 k Ω K T E₂)).V
          →ₗ[Coeff] (localUnitsK (k := k) w).V from
        (Work.SSGRoute.homRepPre (Rep.res (decompK (k := k) w).subtype (Eprime 2 k Ω K T E))
          (Rep.res (decompK (k := k) w).subtype (Eprime 2 k Ω K T E₂))
          (localUnitsK (k := k) w) (Rep.resMap (decompK (k := k) w).subtype F')).hom (Ψ e)) m
    rw [hpp_apply]
    exact hnat e m
  have s3 := mapH1_coeff_comp (G := ↥(decompK (k := k) w)) (A := E) (A' := E₂)
    (B := (Rep.res (decompK (k := k) w).subtype (Eprime 2 k Ω K T E)).V
      →ₗ[Coeff] (localUnitsK (k := k) w).V)
    (B' := (Rep.res (decompK (k := k) w).subtype (Eprime 2 k Ω K T E₂)).V
      →ₗ[Coeff] (localUnitsK (k := k) w).V)
    (f := (f : E →+ E₂)) hf_D (Ψ := Ψ.toAddMonoidHom) hΦ (Ψ' := Ψ₂.toAddMonoidHom) hΦ₂
    (g := (Work.SSGRoute.homRepPre (Rep.res (decompK (k := k) w).subtype (Eprime 2 k Ω K T E))
      (Rep.res (decompK (k := k) w).subtype (Eprime 2 k Ω K T E₂))
      (localUnitsK (k := k) w) (Rep.resMap (decompK (k := k) w).subtype F')).hom.toAddMonoidHom)
    (Work.SSGRoute.homRepPre_isEquivariant
      (Rep.res (decompK (k := k) w).subtype (Eprime 2 k Ω K T E))
      (Rep.res (decompK (k := k) w).subtype (Eprime 2 k Ω K T E₂))
      (localUnitsK (k := k) w) (Rep.resMap (decompK (k := k) w).subtype F'))
    hEq
    (Work.SSGRoute.ArchDictionary.cycTransfer (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink w hw hne
      E (Work.SSGRoute.ArchDictionary.acH1Equiv K c E x))
  rw [s1, s2, s3]

end Work.SSGRoute.ArchDictionary
