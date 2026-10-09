import Mathlib
import Submission.Work.SSGRoute.ArchDictionary.Defs
import Submission.Work.SSGRoute.E1aClean.extResCompOfExtension
import Submission.Work.SSGRoute.ext_h1_bridge
import Submission.Work.SSGRoute.ExtChain.resH2_zpowers_e1aChainH_eq_zero_of_extRes_zpowers_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ArchDictionary

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

attribute [local instance 10000] Rep.hV2 Rep.hV1

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField K]

/-- **The extension criterion, `⟹` direction** (the converse of the proved
`E1aClean.extResCompOfExtension`): if the localisation of a `PhiE`-generator at the decomposition
group of `q` vanishes after the coefficient change `Kˣ → K_qˣ`, then the coefficient-changed
primitive extends to a `D_q`-equivariant map on the canonical cover.

This is `ExtChain.exists_lift_of_extRes_PhiE_eq_zero` with an *arbitrary* coefficient map `ι`
(instead of the identity of `unitsK`): the kernel criterion `ext_connecting_range_ker` is applied
to the mapped short exact sequence `(freeCoverSES M).map (Rep.resFunctor f)`.

(Note: the statement the lemma was originally requested with had the first variable specialised to
`kernel (freeCover N)`; that is the special case recorded at the end of this file, and it is not the
one the archimedean application needs, where the first variable is the coefficient module
`Eprime p k Ω K T E` itself.) -/
theorem exists_extension_of_extRes_comp_mk0_eq_zero
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (q : NK.GlobalCFT.Place ↥K)
    (w : CategoryTheory.Abelian.Ext.{0}
        (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K) M)
        (SSGRoute.PTExt.unitsK k ↥K) 0)
    (h : (SSGRoute.PTExt.extRes (SSGRoute.PTExt.decompK (k := k) q).subtype
        (Work.SSGRoute.ExtChain.E1cGeneric.PhiE (k := k) (Ω := Ω) (K := K) M w)).comp
      (CategoryTheory.Abelian.Ext.mk₀
        (NK.HassePrinciple.unitsToLocalUnits k ↥K q)) (add_zero 1) = 0) :
    ∃ φ : Rep.res (SSGRoute.PTExt.decompK (k := k) q).subtype
        (Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K) M)
        ⟶ SSGRoute.PTExt.localUnitsK (k := k) q,
      ∀ r : (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K) M).V,
        Rep.Hom.hom φ (Work.SSGRoute.ExtChain.E1cGeneric.kappa (k := k) (Ω := Ω) (K := K) M r)
          = (NK.HassePrinciple.unitsToLocalUnitsHom q).toAdditive
              (Rep.Hom.hom (CategoryTheory.Abelian.Ext.addEquiv₀ w) r) := by
  classical
  haveI : Fintype (K ≃ₐ[k] K) := inferInstance
  haveI : Fintype ↥(SSGRoute.PTExt.decompK (k := k) q) := Fintype.ofFinite _
  let F : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) ⥤
      Rep.{0} SSGRoute.PTExt.Coeff ↥(SSGRoute.PTExt.decompK (k := k) q) :=
    Rep.resFunctor (SSGRoute.PTExt.decompK (k := k) q).subtype
  haveI hproj : Projective ((Work.SSGRoute.freeCoverSES M).map F).X₂ :=
    Functor.projective_obj F (Work.SSGRoute.freeCoverSES M).X₂
  have hS : ((Work.SSGRoute.freeCoverSES M).map F).ShortExact :=
    (Work.SSGRoute.freeCoverSES_shortExact M).map_of_exact F
  -- `PhiE` commutes with the restriction of the group
  have hnat : ∀ (hh : 1 + 0 = 1),
      Abelian.Ext.mapExactFunctor F ((Work.SSGRoute.freeCoverSES_shortExact M).extClass.comp w hh)
        = hS.extClass.comp (Abelian.Ext.mapExactFunctor F w) hh := by
    intro hh
    rw [Abelian.Ext.mapExactFunctor_comp F (Work.SSGRoute.freeCoverSES_shortExact M).extClass w hh,
      Abelian.Ext.mapExactFunctor_extClass F (Work.SSGRoute.freeCoverSES_shortExact M)]
    try rfl
  -- the transported hypothesis: the composite class vanishes
  have h1 : (Abelian.Ext.mapExactFunctor F
        ((Work.SSGRoute.freeCoverSES_shortExact M).extClass.comp w (by norm_num : 1 + 0 = 1))).comp
      (Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k ↥K q)) (add_zero 1) = 0 := h
  have haux : (hS.extClass.comp (Abelian.Ext.mapExactFunctor F w) (by norm_num : 1 + 0 = 1)).comp
        (Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k ↥K q)) (add_zero 1)
      = (Abelian.Ext.mapExactFunctor F
          ((Work.SSGRoute.freeCoverSES_shortExact M).extClass.comp w
            (by norm_num : 1 + 0 = 1))).comp
          (Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k ↥K q)) (add_zero 1) :=
    (congrArg (fun z => z.comp (Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k ↥K q))
      (add_zero 1)) (hnat (by norm_num : 1 + 0 = 1))).symm
  -- the `Ext⁰` class whose connecting image is the localised class
  have h2 : hS.extClass.comp
      ((Abelian.Ext.mapExactFunctor F w).comp
        (Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k ↥K q)) (zero_add 0))
      (by norm_num : 1 + 0 = 1) = 0 := by
    refine (Abelian.Ext.comp_assoc hS.extClass (Abelian.Ext.mapExactFunctor F w)
      (Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k ↥K q))
      (by norm_num : 1 + 0 = 1) (zero_add 0) (by norm_num : 1 + 0 + 0 = 1)).symm.trans ?_
    exact haux.trans h1
  obtain ⟨x₂, hx₂'⟩ := Abelian.Ext.contravariant_sequence_exact₁ hS
    (SSGRoute.PTExt.localUnitsK (k := k) q)
    ((Abelian.Ext.mapExactFunctor F w).comp
      (Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k ↥K q)) (zero_add 0))
    (n₁ := 1) (by norm_num : 1 + 0 = 1) h2
  -- work in the `F.obj`-flavour, so that every rewriting step matches syntactically
  let x₂m : Abelian.Ext (F.obj (Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K) M))
      (SSGRoute.PTExt.localUnitsK (k := k) q) 0 := x₂
  have hx₂m : (Abelian.Ext.mk₀
        (F.map (CategoryTheory.Limits.kernel.ι (Work.SSGRoute.freeCover M)))).comp x₂m (zero_add 0)
      = (Abelian.Ext.mapExactFunctor F w).comp
          (Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k ↥K q)) (zero_add 0) := hx₂'
  -- identify the class of the pullback of the restricted primitive
  have hw : Abelian.Ext.mapExactFunctor F w = Abelian.Ext.mk₀ (F.map (Abelian.Ext.addEquiv₀ w)) :=
    (by simpa only [Abelian.Ext.mk₀_addEquiv₀_apply] using
      Abelian.Ext.mapExactFunctor_mk₀ F (Abelian.Ext.addEquiv₀ w))
  have ha : (Abelian.Ext.mapExactFunctor F w).comp
        (Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k ↥K q)) (zero_add 0)
      = Abelian.Ext.mk₀ (F.map (Abelian.Ext.addEquiv₀ w)
          ≫ NK.HassePrinciple.unitsToLocalUnits k ↥K q) := by
    rw [hw, Abelian.Ext.mk₀_comp_mk₀]
  have hmk : Abelian.Ext.mk₀ (F.map (CategoryTheory.Limits.kernel.ι (Work.SSGRoute.freeCover M))
        ≫ Abelian.Ext.addEquiv₀ x₂m)
      = (Abelian.Ext.mapExactFunctor F w).comp
          (Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k ↥K q)) (zero_add 0) := by
    have hstep : (Abelian.Ext.mk₀
          (F.map (CategoryTheory.Limits.kernel.ι (Work.SSGRoute.freeCover M)))).comp x₂m (zero_add 0)
        = (Abelian.Ext.mk₀
            (F.map (CategoryTheory.Limits.kernel.ι (Work.SSGRoute.freeCover M)))).comp
              (Abelian.Ext.mk₀ (Abelian.Ext.addEquiv₀ x₂m)) (zero_add 0) := by
      rw [Abelian.Ext.mk₀_addEquiv₀_apply x₂m]
    rw [← hx₂m, hstep, Abelian.Ext.mk₀_comp_mk₀]
  have hm : F.map (CategoryTheory.Limits.kernel.ι (Work.SSGRoute.freeCover M))
        ≫ Abelian.Ext.addEquiv₀ x₂m
      = F.map (Abelian.Ext.addEquiv₀ w) ≫ NK.HassePrinciple.unitsToLocalUnits k ↥K q := by
    have hh := congrArg Abelian.Ext.addEquiv₀ (hmk.trans ha)
    rw [Work.SSGRoute.ExtChain.addEquiv₀_mk₀, Work.SSGRoute.ExtChain.addEquiv₀_mk₀] at hh
    exact hh
  have hιapp : ∀ y : (SSGRoute.PTExt.unitsK k ↥K).V,
      Rep.Hom.hom (NK.HassePrinciple.unitsToLocalUnits k ↥K q) y
        = (NK.HassePrinciple.unitsToLocalUnitsHom q).toAdditive y := fun _ => rfl
  refine ⟨Abelian.Ext.addEquiv₀ x₂m, fun r => ?_⟩
  have hval := congrArg (fun (g : F.obj (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1
      (k := k) (Ω := Ω) (K := K) M) ⟶ SSGRoute.PTExt.localUnitsK (k := k) q) =>
        Rep.Hom.hom g r) hm
  rw [Rep.comp_apply, Rep.comp_apply] at hval
  rw [Work.SSGRoute.ExtChain.resMap_kernel_apply, Work.SSGRoute.ExtChain.resMap_addEquiv₀_apply,
    hιapp] at hval
  exact hval

/-- The form of `exists_extension_of_extRes_comp_mk0_eq_zero` in which the first variable is the
canonical syzygy `kernel (freeCover N)` of a coefficient module `N`. -/
theorem exists_extension_of_extRes_comp_mk0_eq_zero_syzygy
    (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite N.V]
    (q : NK.GlobalCFT.Place ↥K)
    (w : CategoryTheory.Abelian.Ext.{0}
        (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K)
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)))
        (SSGRoute.PTExt.unitsK k ↥K) 0)
    (h : (SSGRoute.PTExt.extRes (SSGRoute.PTExt.decompK (k := k) q).subtype
        (Work.SSGRoute.ExtChain.E1cGeneric.PhiE (k := k) (Ω := Ω) (K := K)
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) w)).comp
      (CategoryTheory.Abelian.Ext.mk₀
        (NK.HassePrinciple.unitsToLocalUnits k ↥K q)) (add_zero 1) = 0) :
    ∃ φ : Rep.res (SSGRoute.PTExt.decompK (k := k) q).subtype
        (Work.SSGRoute.ExtChain.E1cGeneric.E1cF (k := k) (Ω := Ω) (K := K)
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)))
        ⟶ SSGRoute.PTExt.localUnitsK (k := k) q,
      ∀ r : (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := k) (Ω := Ω) (K := K)
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N))).V,
        Rep.Hom.hom φ (Work.SSGRoute.ExtChain.E1cGeneric.kappa (k := k) (Ω := Ω) (K := K)
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) r)
          = (NK.HassePrinciple.unitsToLocalUnitsHom q).toAdditive
              (Rep.Hom.hom (CategoryTheory.Abelian.Ext.addEquiv₀ w) r) :=
  exists_extension_of_extRes_comp_mk0_eq_zero
    (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) q w h

end

end Work.SSGRoute.ArchDictionary
