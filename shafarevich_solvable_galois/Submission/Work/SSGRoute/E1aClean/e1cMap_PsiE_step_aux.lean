import Mathlib
import Submission.Work.SSGRoute.E1aClean.LevelChangeDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # The `ΨE`-step of the level-change square (auxiliary form)

Proves `Work.SSGRoute.E1aClean.e1cMap_PsiE_step_aux` together with the ingredients it needs:

* `e1cLC_ext_addEquiv₀_comp_mk₀`, `e1cLC_ext_addEquiv₀_mapExt` — the `Ext⁰` computation for a
  Yoneda class left-composed with a functor image;
* `e1cLC_addEquiv₀_gen` — the resulting identification of `addEquiv₀` of the transported generator;
* `e1cLC_PsiEMap_val` — the `rfl`-level value formula for `ΨE = PsiEMap`;
* `e1cLC_toCoindFun_comp_resMap` — the pointwise formula for `toCoindFun` on a composite with a
  restricted morphism;
* `e1cLC_genExt` / `e1cLC_genMap` — short names for the transported generator and its `Ext⁰`-image
  (the spelled-out terms are extremely costly for the elaborator, and these make the proof cheap).
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 20000

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt

noncomputable section

/-! ## Auxiliary `Ext⁰` lemmas -/

/-- `addEquiv₀` of a Yoneda class left-composed with a degree-`0` class is the composite of the
corresponding morphisms. -/
theorem e1cLC_ext_addEquiv₀_comp_mk₀ {C : Type*} [Category C] [Abelian C] [HasExt C]
    {X Y Z : C} (f : X ⟶ Y) (β : Abelian.Ext Y Z 0) :
    Abelian.Ext.addEquiv₀ ((Abelian.Ext.mk₀ f).comp β (zero_add 0))
      = f ≫ Abelian.Ext.addEquiv₀ β := by
  have h : Abelian.Ext.mk₀ (Abelian.Ext.addEquiv₀ ((Abelian.Ext.mk₀ f).comp β (zero_add 0)))
      = Abelian.Ext.mk₀ (f ≫ Abelian.Ext.addEquiv₀ β) := by
    rw [Abelian.Ext.mk₀_addEquiv₀_apply]
    conv_lhs => rw [← Abelian.Ext.mk₀_addEquiv₀_apply β]
    rw [Abelian.Ext.mk₀_comp_mk₀]
  exact (Abelian.Ext.mk₀_bijective X Z).1 h

/-- `addEquiv₀` commutes with an exact functor: it is the functorial image of the morphism. -/
theorem e1cLC_ext_addEquiv₀_mapExt {C D : Type*} [Category C] [Category D] [Abelian C]
    [Abelian D] [HasExt C] [HasExt D]
    (F : C ⥤ D) [F.Additive] [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    {X Y : C} (e : Abelian.Ext X Y 0) :
    Abelian.Ext.addEquiv₀ (F.mapExtAddHom X Y 0 e) = F.map (Abelian.Ext.addEquiv₀ e) := by
  rw [show F.mapExtAddHom X Y 0 e = Abelian.Ext.mapExactFunctor F e from rfl]
  rw [Abelian.Ext.mapExactFunctor₀]
  simp only [Function.comp_apply]
  rw [Abelian.Ext.homEquiv₀_symm_apply]
  have hmk : Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ (F.map (Abelian.Ext.homEquiv₀ e)))
      = F.map (Abelian.Ext.homEquiv₀ e) := by
    have h : Abelian.Ext.mk₀
        (Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ (F.map (Abelian.Ext.homEquiv₀ e))))
        = Abelian.Ext.mk₀ (F.map (Abelian.Ext.homEquiv₀ e)) := by
      rw [Abelian.Ext.mk₀_addEquiv₀_apply]
    exact (Abelian.Ext.mk₀_bijective (F.obj X) (F.obj Y)).1 h
  rw [hmk]
  rfl

variable {k : Type} [Field k] [CharZero k] {Ω : Type} [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]

/-- The value formula for `ΨE = PsiEMap`: it is `toCoindFun` of the `addEquiv₀`-image. -/
theorem e1cLC_PsiEMap_val {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (X : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (x : Abelian.Ext X (SSGRoute.PTExt.unitsK k K) 0) :
    Subtype.val (Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap (k := k) (Ω := Ω) (K := K) X x)
      = Work.SSGRoute.toCoindFun X (Abelian.Ext.addEquiv₀ x) := by
  have h := Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap_apply_toCoindH0
    (k := k) (Ω := Ω) (K := K) X x
  exact (congrArg Subtype.val h).trans
    (Work.SSGRoute.toCoindH0_apply_coe X (Abelian.Ext.addEquiv₀ x))

/-- `toCoindFun` on a composite with a restricted morphism: the restricted map acts by
precomposition on the `toCoindFun` of the level-`k` morphism. -/
theorem e1cLC_toCoindFun_comp_resMap {K : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K]
    (L : IntermediateField k K) [FiniteDimensional ↥L (Kover L)] [IsGalois ↥L (Kover L)]
    {M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)}
    {M' : Rep.{0} SSGRoute.PTExt.Coeff (↥(Kover L) ≃ₐ[↥L] ↥(Kover L))}
    (g : M' ⟶ Rep.res (galKIncl L) M) (f : M ⟶ SSGRoute.PTExt.unitsK k K) :
    Work.SSGRoute.toCoindFun (k := ↥L) (Ω := Ω) (K := Kover L) M'
        (g ≫ Rep.resMap (galKIncl L) f)
      = Work.SSGRoute.precompAddHom (Rep.Hom.hom g).toAddMonoidHom
          (Work.SSGRoute.toCoindFun (k := k) (Ω := Ω) (K := K) M f) := by
  apply AddMonoidHom.ext
  intro x
  rw [Work.SSGRoute.precompAddHom_apply, AddMonoidHom.comp_apply]
  rw [Work.SSGRoute.toCoindFun_apply, Work.SSGRoute.toCoindFun_apply]
  rfl

variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField K]

/-- The `Ext⁰`-computation behind the `ΨE`-step: the transported generator is `mk₀` of the
comparison composed with the `addEquiv₀` of `w`. -/
theorem e1cLC_addEquiv₀_gen (L : IntermediateField k K)
    [FiniteDimensional ↥L (Kover L)] [IsGalois ↥L (Kover L)] [NumberField (Kover L)]
    (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite R.V]
    (w : Abelian.Ext.{0} (e1cLC_R1k R) (SSGRoute.PTExt.unitsK k K) 0) :
    Abelian.Ext.addEquiv₀
        (Abelian.Ext.comp (Abelian.Ext.mk₀ (e1cLC_coverCompat L R).τ₁)
          ((Rep.resFunctor (k := SSGRoute.PTExt.Coeff) (galKIncl L)).mapExtAddHom
            (e1cLC_R1k R) (SSGRoute.PTExt.unitsK k K) 0 w) (zero_add 0))
      = (e1cLC_coverCompat L R).τ₁ ≫ Rep.resMap (galKIncl L) (Abelian.Ext.addEquiv₀ w) := by
  rw [show Abelian.Ext.addEquiv₀
        (Abelian.Ext.comp (Abelian.Ext.mk₀ (e1cLC_coverCompat L R).τ₁)
          ((Rep.resFunctor (k := SSGRoute.PTExt.Coeff) (galKIncl L)).mapExtAddHom
            (e1cLC_R1k R) (SSGRoute.PTExt.unitsK k K) 0 w) (zero_add 0))
      = (e1cLC_coverCompat L R).τ₁ ≫ Abelian.Ext.addEquiv₀
          (((Rep.resFunctor (k := SSGRoute.PTExt.Coeff) (galKIncl L)).mapExtAddHom
            (e1cLC_R1k R) (SSGRoute.PTExt.unitsK k K) 0 w)) from
    e1cLC_ext_addEquiv₀_comp_mk₀ _ _]
  congr 1
  exact e1cLC_ext_addEquiv₀_mapExt _ _

/-- The transported generator `mk₀ Φ.τ₁ ∘ F.mapExtAddHom w` of the level-change square. -/
abbrev e1cLC_genExt (L : IntermediateField k K)
    [FiniteDimensional ↥L (Kover L)] [IsGalois ↥L (Kover L)] [NumberField (Kover L)]
    (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite R.V]
    (w : Abelian.Ext.{0} (e1cLC_R1k R) (SSGRoute.PTExt.unitsK k K) 0) :=
  Abelian.Ext.comp (Abelian.Ext.mk₀ (e1cLC_coverCompat L R).τ₁)
    ((Rep.resFunctor (k := SSGRoute.PTExt.Coeff) (galKIncl L)).mapExtAddHom
      (e1cLC_R1k R) (SSGRoute.PTExt.unitsK k K) 0 w) (zero_add 0)

/-- The `Ext⁰`-image of the transported generator, with the category of its source and target
pinned down explicitly (this is what keeps the `HasExt` instance search cheap). -/
abbrev e1cLC_genMap (L : IntermediateField k K)
    [FiniteDimensional ↥L (Kover L)] [IsGalois ↥L (Kover L)] [NumberField (Kover L)]
    (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite R.V]
    (w : Abelian.Ext.{0} (e1cLC_R1k R) (SSGRoute.PTExt.unitsK k K) 0) :=
  Abelian.Ext.addEquiv₀ (X := e1cLC_R1L L R)
    (Y := Rep.res (galKIncl L) (SSGRoute.PTExt.unitsK k K)) (e1cLC_genExt L R w)

theorem e1cMap_PsiE_step_aux {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [NumberField K] (L : IntermediateField k K)
    [FiniteDimensional ↥L (Work.SSGRoute.E1aClean.Kover L)]
    [IsGalois ↥L (Work.SSGRoute.E1aClean.Kover L)]
    [NumberField (Work.SSGRoute.E1aClean.Kover L)]
    (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite R.V]
    (w : CategoryTheory.Abelian.Ext.{0} (Work.SSGRoute.E1aClean.e1cLC_R1k R)
      (SSGRoute.PTExt.unitsK k K) 0) :
    Subtype.val (Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap (k := ↥L) (Ω := Ω)
        (K := Work.SSGRoute.E1aClean.Kover L)
        (Work.SSGRoute.E1aClean.e1cLC_R1L L R)
        (CategoryTheory.Abelian.Ext.comp
          (CategoryTheory.Abelian.Ext.mk₀ (Work.SSGRoute.E1aClean.e1cLC_coverCompat L R).τ₁)
          ((Rep.resFunctor (k := SSGRoute.PTExt.Coeff)
            (Work.SSGRoute.E1aClean.galKIncl L)).mapExtAddHom
            (Work.SSGRoute.E1aClean.e1cLC_R1k R) (SSGRoute.PTExt.unitsK k K) 0 w) (zero_add 0)))
      = Work.SSGRoute.E1aClean.e1cLC_π L R
          (Subtype.val (Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap (k := k) (Ω := Ω) (K := K)
            (Work.SSGRoute.E1aClean.e1cLC_R1k R) w)) := by
  have hL : Subtype.val (Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap (k := ↥L) (Ω := Ω)
        (K := Kover L) (e1cLC_R1L L R) (e1cLC_genExt L R w))
      = Work.SSGRoute.toCoindFun (k := ↥L) (Ω := Ω) (K := Kover L) (e1cLC_R1L L R)
          (e1cLC_genMap L R w) := by
    have h := Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap_apply_toCoindH0
      (k := ↥L) (Ω := Ω) (K := Kover L) (e1cLC_R1L L R) (e1cLC_genExt L R w)
    exact (congrArg Subtype.val h).trans
      (Work.SSGRoute.toCoindH0_apply_coe (k := ↥L) (Ω := Ω) (K := Kover L)
        (e1cLC_R1L L R) (e1cLC_genMap L R w))
  calc
    Subtype.val (Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap (k := ↥L) (Ω := Ω)
        (K := Kover L) (e1cLC_R1L L R) (e1cLC_genExt L R w))
        = Work.SSGRoute.toCoindFun (k := ↥L) (Ω := Ω) (K := Kover L) (e1cLC_R1L L R)
            (e1cLC_genMap L R w) := hL
    _ = Work.SSGRoute.toCoindFun (k := ↥L) (Ω := Ω) (K := Kover L) (e1cLC_R1L L R)
          ((e1cLC_coverCompat L R).τ₁ ≫ Rep.resMap (galKIncl L) (Abelian.Ext.addEquiv₀ w)) :=
        congrArg (fun z => Work.SSGRoute.toCoindFun (k := ↥L) (Ω := Ω) (K := Kover L)
          (e1cLC_R1L L R) z) (e1cLC_addEquiv₀_gen L R w)
    _ = e1cLC_π L R
          (Work.SSGRoute.toCoindFun (k := k) (Ω := Ω) (K := K) (e1cLC_R1k R)
            (Abelian.Ext.addEquiv₀ w)) :=
        e1cLC_toCoindFun_comp_resMap (L := L) (M := e1cLC_R1k R) (M' := e1cLC_R1L L R)
          (e1cLC_coverCompat L R).τ₁ (Abelian.Ext.addEquiv₀ w)
    _ = e1cLC_π L R
          (Subtype.val (Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap (k := k) (Ω := Ω) (K := K)
            (e1cLC_R1k R) w)) := by
        rw [e1cLC_PsiEMap_val (k := k) (Ω := Ω) (K := K) (e1cLC_R1k R) w]

end

end Work.SSGRoute.E1aClean
