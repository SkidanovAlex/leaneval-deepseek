import Mathlib.FieldTheory.KrullTopology
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Basic.Complex.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.ArchDictionary.archSeamDefs2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ArchDictionary

open CategoryTheory CategoryTheory.Limits SSGRoute.PTExt Work.SSGRoute.ArchDictionary
  Work.SSGRoute.ArchDictionary.ArchSeamP2

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false

theorem ss2SquareLHS {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K]
    (T : Type) [AddCommGroup T] [Module (ZMod 2) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) T]
    (hζ : IsPrimitiveRoot (-1 : Ω) 2) (hζK : (-1 : Ω) ∈ K)
    (hT : SSGRoute.IsCyclotomicDual 2 (T := T) (SSGRoute.res k K) (-1 : Ω))
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (hne : decompK (k := k) (seamPlace (K := K) φ) ≠ ⊥)
    (E : Type) [AddCommGroup E] [Module (ZMod 2) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) E] [Finite E]
    (Ψ : E ≃+ ((Eprime 2 k Ω K T E).V →ₗ[Coeff]
      (localUnitsK (k := k) (seamPlace (K := K) φ)).V))
    (hΦ : @Work.GroupCohomology.IsEquivariant ↥(decompK (k := k) (seamPlace (K := K) φ)) E
      ((Eprime 2 k Ω K T E).V →ₗ[Coeff] (localUnitsK (k := k) (seamPlace (K := K) φ)).V) _ _ _
      (dcAct K E (seamPlace (K := K) φ))
      (Work.SSGRoute.homRepDistribMulAction
        (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E))
        (localUnitsK (k := k) (seamPlace (K := K) φ)))
      Ψ.toAddMonoidHom)
    (hΨ : @Work.GroupCohomology.IsEquivariant ↥(decompK (k := k) (seamPlace (K := K) φ))
      ((Eprime 2 k Ω K T E).V →ₗ[Coeff] (localUnitsK (k := k) (seamPlace (K := K) φ)).V) E _ _ _
      (Work.SSGRoute.homRepDistribMulAction
        (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E))
        (localUnitsK (k := k) (seamPlace (K := K) φ)))
      (dcAct K E (seamPlace (K := K) φ)) Ψ.symm.toAddMonoidHom)
    (b : (Ω ≃ₐ[k] Ω) → E) (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b)
    (hl : SSGRoute.IsLocConstOn ⊤ b) :
    ∃ (ψZ : ↥(decompK (k := k) (seamPlace (K := K) φ)) →
        ((Eprime 2 k Ω K T E).V →ₗ[Coeff]
          (localUnitsK (k := k) (seamPlace (K := K) φ)).V))
      (hz : ψZ ∈ @Work.GroupCohomology.Z1 ↥(decompK (k := k) (seamPlace (K := K) φ))
        ((Eprime 2 k Ω K T E).V →ₗ[Coeff]
          (localUnitsK (k := k) (seamPlace (K := K) φ)).V) _ _
        (Work.SSGRoute.homRepDistribMulAction
          (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E))
          (localUnitsK (k := k) (seamPlace (K := K) φ)))),
      (NatH1.eOf (N := localUnitsK (k := k) (seamPlace (K := K) φ))
          (moduleInjective_coeff_of_divisible _
            (localUnitsK_divisible_of_decompK_ne_bot (k := k) (Ω := Ω) (K := K) φ
              (seamPlace (K := K) φ) rfl hne))
          (fun M => Classical.choose (homRepFree_coind_iso _ M.V _))
          (fun M => Classical.choose_spec (homRepFree_coind_iso _ M.V _))
          (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E)))
          (archPhiOf c hc2 hc1 φ hlink (seamPlace (K := K) φ) rfl hne E
            (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E))
            Ψ hΦ hΨ (AcOfFun (K := K) (E := E) c b))
        = @Work.GroupCohomology.H1π ↥(decompK (k := k) (seamPlace (K := K) φ))
            ((Eprime 2 k Ω K T E).V →ₗ[Coeff]
              (localUnitsK (k := k) (seamPlace (K := K) φ)).V) _ _
            (Work.SSGRoute.homRepDistribMulAction
              (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E))
              (localUnitsK (k := k) (seamPlace (K := K) φ))) ⟨ψZ, hz⟩ ∧
      (∀ g : ↥(decompK (k := k) (seamPlace (K := K) φ)),
        ψZ g = Ψ (b (((ePowLift (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink
          (seamPlace (K := K) φ) rfl hne).symm g : ↥(Subgroup.zpowers c)) : Ω ≃ₐ[k] Ω))) := by
  classical
  letI hcycΩ : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  letI hcyc : DistribMulAction ↥(Subgroup.zpowers c) E := cycAct K c E
  letI hInst : DistribMulAction ↥(decompK (k := k) (seamPlace (K := K) φ))
      ((Eprime 2 k Ω K T E).V →ₗ[Coeff]
        (localUnitsK (k := k) (seamPlace (K := K) φ)).V) :=
    Work.SSGRoute.homRepDistribMulAction
      (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E))
      (localUnitsK (k := k) (seamPlace (K := K) φ))
  -- **Step 1.**  The left-hand side, pushed through the `eOf` dictionary, is the coefficient
  -- change of the transferred class of `b|⟨c⟩`.
  have hE1 : (NatH1.eOf (N := localUnitsK (k := k) (seamPlace (K := K) φ))
        (moduleInjective_coeff_of_divisible _
          (localUnitsK_divisible_of_decompK_ne_bot (k := k) (Ω := Ω) (K := K) φ
            (seamPlace (K := K) φ) rfl hne))
        (fun M => Classical.choose (homRepFree_coind_iso _ M.V _))
        (fun M => Classical.choose_spec (homRepFree_coind_iso _ M.V _))
        (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E)))
      (archPhiOf c hc2 hc1 φ hlink (seamPlace (K := K) φ) rfl hne E
        (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E))
        Ψ hΦ hΨ (AcOfFun (K := K) (E := E) c b))
      = (@Work.GroupCohomology.mapH1 ↥(decompK (k := k) (seamPlace (K := K) φ)) E
          ((Eprime 2 k Ω K T E).V →ₗ[Coeff]
            (localUnitsK (k := k) (seamPlace (K := K) φ)).V) _ _ _
          (dcAct K E (seamPlace (K := K) φ))
          (Work.SSGRoute.homRepDistribMulAction
            (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E))
            (localUnitsK (k := k) (seamPlace (K := K) φ)))
          Ψ.toAddMonoidHom hΦ)
        (cycTransfer (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink
          (seamPlace (K := K) φ) rfl hne E
          (acH1Equiv K c E (AcOfFun (K := K) (E := E) c b))) := by
    rw [show archPhiOf c hc2 hc1 φ hlink (seamPlace (K := K) φ) rfl hne E
          (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E))
          Ψ hΦ hΨ (AcOfFun (K := K) (E := E) c b)
        = (NatH1.eOf (N := localUnitsK (k := k) (seamPlace (K := K) φ))
            (moduleInjective_coeff_of_divisible _
              (localUnitsK_divisible_of_decompK_ne_bot (k := k) (Ω := Ω) (K := K) φ
                (seamPlace (K := K) φ) rfl hne))
            (fun M => Classical.choose (homRepFree_coind_iso _ M.V _))
            (fun M => Classical.choose_spec (homRepFree_coind_iso _ M.V _))
            (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype
              (Eprime 2 k Ω K T E))).symm
          ((@Work.GroupCohomology.mapH1 ↥(decompK (k := k) (seamPlace (K := K) φ)) E
            ((Eprime 2 k Ω K T E).V →ₗ[Coeff]
              (localUnitsK (k := k) (seamPlace (K := K) φ)).V) _ _ _
            (dcAct K E (seamPlace (K := K) φ))
            (Work.SSGRoute.homRepDistribMulAction
              (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E))
              (localUnitsK (k := k) (seamPlace (K := K) φ)))
            Ψ.toAddMonoidHom hΦ)
            (cycTransfer (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink
              (seamPlace (K := K) φ) rfl hne E
              (acH1Equiv K c E (AcOfFun (K := K) (E := E) c b)))) from rfl]
    rw [AddEquiv.apply_symm_apply]
  -- **Step 2.**  An explicit cocycle representing the transferred class.
  let ψZc : ↥(Work.GroupCohomology.Z1 ↥(decompK (k := k) (seamPlace (K := K) φ))
      ((Eprime 2 k Ω K T E).V →ₗ[Coeff]
        (localUnitsK (k := k) (seamPlace (K := K) φ)).V)) :=
    Work.GroupCohomology.mapZ1 ↥(decompK (k := k) (seamPlace (K := K) φ)) Ψ.toAddMonoidHom hΦ
      (Work.SSGRoute.PT.pushZ1
        (ePowLift (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink (seamPlace (K := K) φ) rfl hne)
        (AddEquiv.refl E)
        (ePowLift_compat c hc2 hc1 φ hlink (seamPlace (K := K) φ) rfl hne E)
        (acRho K c E ⟨b, mem_Zc_of_global (K := K) (E := E) (c := c) hb⟩))
  -- **Step 3.**  The class of `ψZc` is the coefficient change of the transferred class.
  have hLHS : (Work.GroupCohomology.mapH1 ↥(decompK (k := k) (seamPlace (K := K) φ))
        Ψ.toAddMonoidHom hΦ)
      (cycTransfer (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink
        (seamPlace (K := K) φ) rfl hne E
        (acH1Equiv K c E (AcOfFun (K := K) (E := E) c b)))
      = Work.GroupCohomology.H1π ↥(decompK (k := k) (seamPlace (K := K) φ))
          ((Eprime 2 k Ω K T E).V →ₗ[Coeff]
            (localUnitsK (k := k) (seamPlace (K := K) φ)).V) ψZc := by
    rw [show AcOfFun (K := K) (E := E) c b
        = Acπ (K := K) (E := E) c ⟨b, mem_Zc_of_global (K := K) (E := E) (c := c) hb⟩ from
      AcOfFun_eq (K := K) (E := E) c b _]
    rw [Acπ_apply, acH1Equiv_apply, acToH1_mk]
    rw [show cycTransfer (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink
          (seamPlace (K := K) φ) rfl hne E
          (Work.GroupCohomology.H1π ↥(Subgroup.zpowers c) E
            (acRho K c E ⟨b, mem_Zc_of_global (K := K) (E := E) (c := c) hb⟩))
        = Work.SSGRoute.PT.pushH1
            (ePowLift (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink
              (seamPlace (K := K) φ) rfl hne)
            (AddEquiv.refl E)
            (ePowLift_compat c hc2 hc1 φ hlink (seamPlace (K := K) φ) rfl hne E)
            (Work.GroupCohomology.H1π ↥(Subgroup.zpowers c) E
              (acRho K c E ⟨b, mem_Zc_of_global (K := K) (E := E) (c := c) hb⟩)) from rfl]
    rw [Work.SSGRoute.PT.pushH1_H1π]
    rw [show ψZc = Work.GroupCohomology.mapZ1 ↥(decompK (k := k) (seamPlace (K := K) φ))
          Ψ.toAddMonoidHom hΦ
          (Work.SSGRoute.PT.pushZ1
            (ePowLift (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink
              (seamPlace (K := K) φ) rfl hne)
            (AddEquiv.refl E)
            (ePowLift_compat c hc2 hc1 φ hlink (seamPlace (K := K) φ) rfl hne E)
            (acRho K c E ⟨b, mem_Zc_of_global (K := K) (E := E) (c := c) hb⟩)) from rfl]
    rw [Work.GroupCohomology.mapH1_H1π ↥(decompK (k := k) (seamPlace (K := K) φ))
      Ψ.toAddMonoidHom hΦ
      (Work.SSGRoute.PT.pushZ1
        (ePowLift (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink (seamPlace (K := K) φ) rfl hne)
        (AddEquiv.refl E)
        (ePowLift_compat c hc2 hc1 φ hlink (seamPlace (K := K) φ) rfl hne E)
        (acRho K c E ⟨b, mem_Zc_of_global (K := K) (E := E) (c := c) hb⟩))]
  -- **Step 4.**  The value rule of `ψZc`.
  have hψZval : ∀ g : ↥(decompK (k := k) (seamPlace (K := K) φ)),
      (ψZc : ↥(decompK (k := k) (seamPlace (K := K) φ)) →
        ((Eprime 2 k Ω K T E).V →ₗ[Coeff]
          (localUnitsK (k := k) (seamPlace (K := K) φ)).V)) g
        = Ψ (b (((ePowLift (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink
            (seamPlace (K := K) φ) rfl hne).symm g : ↥(Subgroup.zpowers c)) : Ω ≃ₐ[k] Ω)) := by
    intro g
    rw [show (ψZc : ↥(decompK (k := k) (seamPlace (K := K) φ)) →
          ((Eprime 2 k Ω K T E).V →ₗ[Coeff]
            (localUnitsK (k := k) (seamPlace (K := K) φ)).V)) g
        = (Work.GroupCohomology.mapZ1 ↥(decompK (k := k) (seamPlace (K := K) φ))
            Ψ.toAddMonoidHom hΦ
            (Work.SSGRoute.PT.pushZ1
              (ePowLift (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink
                (seamPlace (K := K) φ) rfl hne)
              (AddEquiv.refl E)
              (ePowLift_compat c hc2 hc1 φ hlink (seamPlace (K := K) φ) rfl hne E)
              (acRho K c E ⟨b, mem_Zc_of_global (K := K) (E := E) (c := c) hb⟩)) :
            ↥(decompK (k := k) (seamPlace (K := K) φ)) →
              ((Eprime 2 k Ω K T E).V →ₗ[Coeff]
                (localUnitsK (k := k) (seamPlace (K := K) φ)).V)) g from rfl]
    rw [Work.GroupCohomology.mapZ1_coe, Work.GroupCohomology.mapCochain1_apply,
      Work.SSGRoute.PT.pushZ1_coe, Work.SSGRoute.PT.pushCoeff_apply]
    rfl
  refine ⟨(ψZc : ↥(decompK (k := k) (seamPlace (K := K) φ)) →
      ((Eprime 2 k Ω K T E).V →ₗ[Coeff]
        (localUnitsK (k := k) (seamPlace (K := K) φ)).V)),
    ψZc.2, ?_, hψZval⟩
  exact hE1.trans hLHS

end Work.SSGRoute.ArchDictionary
