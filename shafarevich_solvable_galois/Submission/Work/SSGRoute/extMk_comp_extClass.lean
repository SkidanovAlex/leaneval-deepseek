import Mathlib
import Submission.Work.SSGRoute.ExtConeLift.liftCocycle_postcomp_mor3_rightUnshift
import Submission.Work.SSGRoute.ExtConeLift.equivHomShift_symm_comp_add_inv
import Submission.Work.SSGRoute.ExtConeLift.delta_toSingleMk_eq
import Submission.Work.SSGRoute.ExtConeLift.comp_toSingleMk_eq
import Submission.Work.SSGRoute.ExtConeLift.single_delta_eq_triangleOfSES_delta
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open CategoryTheory Limits CochainComplex HomComplex

universe u v w u₁ v₁

set_option maxHeartbeats 1000000 in
/- **The connecting morphism computed by lifting in a mapping cone.** -/
theorem connecting_eq_lift {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)
    {K : CochainComplex C ℤ} {n : ℤ}
    (β : Cochain K S.X₂ n) (α : Cocycle K S.X₁ (n + 1))
    (eq : δ n (n + 1) β + (α : Cochain K S.X₁ (n + 1)).comp
        (Cochain.ofHom S.f) (add_zero (n + 1)) = 0) :
    (ShiftedHom.map (Cocycle.equivHomShift.symm
        ((CochainComplex.mappingCone.liftCocycle S.f α β rfl eq).postcomp
          (CochainComplex.mappingCone.descShortComplex S))) DerivedCategory.Q).comp
      (DerivedCategory.triangleOfSESδ hS) (by lia : 1 + n = n + 1) =
    -(ShiftedHom.map (Cocycle.equivHomShift.symm α) DerivedCategory.Q) := by
  let m3 : CochainComplex.mappingCone S.f ⟶ S.X₁⟦(1:ℤ)⟧ :=
    (CochainComplex.mappingCone.triangle S.f).mor₃
  have hA : ((CochainComplex.mappingCone.liftCocycle S.f α β rfl eq).postcomp m3).rightUnshift
      (n + 1) (by omega) = -α :=
    ExtConeLift.liftCocycle_postcomp_mor3_rightUnshift (β := β) (α := α) eq
  have hB := ExtConeLift.equivHomShift_symm_comp_add_inv
    (z := (CochainComplex.mappingCone.liftCocycle S.f α β rfl eq).postcomp m3)
  have theta : ShiftedHom.comp
      (Cocycle.equivHomShift.symm (CochainComplex.mappingCone.liftCocycle S.f α β rfl eq))
      m3 (by lia : 1 + n = n + 1) = -(Cocycle.equivHomShift.symm α) := by
    simp only [ShiftedHom.comp]
    rw [← Category.assoc]
    rw [← Cocycle.equivHomShift_symm_postcomp (CochainComplex.mappingCone.liftCocycle S.f α β rfl eq) m3]
    rw [hB]
    rw [hA]
    simp
  have hφ : Cocycle.equivHomShift.symm
        ((CochainComplex.mappingCone.liftCocycle S.f α β rfl eq).postcomp
          (CochainComplex.mappingCone.descShortComplex S)) =
      ShiftedHom.comp (Cocycle.equivHomShift.symm (CochainComplex.mappingCone.liftCocycle S.f α β rfl eq))
        (ShiftedHom.mk₀ 0 rfl (CochainComplex.mappingCone.descShortComplex S))
        (by rw [zero_add]) := by
    rw [Cocycle.equivHomShift_symm_postcomp, ShiftedHom.comp_mk₀]
  have step1 : (ShiftedHom.map (Cocycle.equivHomShift.symm
        ((CochainComplex.mappingCone.liftCocycle S.f α β rfl eq).postcomp
          (CochainComplex.mappingCone.descShortComplex S))) DerivedCategory.Q).comp
      (DerivedCategory.triangleOfSESδ hS) (by lia : 1 + n = n + 1) =
      (ShiftedHom.map (Cocycle.equivHomShift.symm (CochainComplex.mappingCone.liftCocycle S.f α β rfl eq))
        DerivedCategory.Q).comp
        (ShiftedHom.map m3 DerivedCategory.Q) (by lia : 1 + n = n + 1) := by
    rw [hφ]
    rw [ShiftedHom.map_comp, ShiftedHom.map_mk₀]
    rw [ShiftedHom.comp_assoc]
    rw [ShiftedHom.mk₀_comp]
    rw [DerivedCategory.descShortComplex_triangleOfSESδ]
    rfl
    all_goals omega
  have step2 : (ShiftedHom.map (Cocycle.equivHomShift.symm (CochainComplex.mappingCone.liftCocycle S.f α β rfl eq))
        DerivedCategory.Q).comp
        (ShiftedHom.map m3 DerivedCategory.Q) (by lia : 1 + n = n + 1) =
      ShiftedHom.map (ShiftedHom.comp
          (Cocycle.equivHomShift.symm (CochainComplex.mappingCone.liftCocycle S.f α β rfl eq))
          m3 (by lia : 1 + n = n + 1)) DerivedCategory.Q :=
    (ShiftedHom.map_comp _ _ _ _).symm
  have hneg : ShiftedHom.map (-(Cocycle.equivHomShift.symm α)) DerivedCategory.Q =
      -(ShiftedHom.map (Cocycle.equivHomShift.symm α) DerivedCategory.Q) := by
    simp [ShiftedHom.map]
  rw [step1, step2, theta, hneg]

/- ## Auxiliary lemmas about shifted homs -/

/-- `ShiftedHom.map` is compatible with negation. -/
lemma shiftedHom_map_neg {C : Type u} [Category.{v} C] [Preadditive C]
    {D : Type u₁} [Category.{v₁} D] [Preadditive D] [HasShift C ℤ] [HasShift D ℤ]
    {X Y : C} {a : ℤ} (f : ShiftedHom X Y a) (F : C ⥤ D) [F.CommShift ℤ] [F.Additive] :
    (-f).map F = -(f.map F) := by
  rw [eq_neg_iff_add_eq_zero, ← ShiftedHom.map_add, neg_add_cancel, ShiftedHom.map_zero]

/-- Precomposing a morphism (which has degree `0`) commutes with `ShiftedHom.comp`. -/
lemma shiftedHom_comp_of_comp {C : Type u} [Category.{v} C] [HasShift C ℤ]
    {X Y Z T : C} {a b c : ℤ} (f : X ⟶ Y) (g : ShiftedHom Y Z a)
    (γ : ShiftedHom Z T b) (h : b + a = c) :
    ShiftedHom.comp (f ≫ g) γ h = f ≫ ShiftedHom.comp g γ h := by
  simp only [ShiftedHom.comp, Category.assoc]

set_option maxHeartbeats 4000000 in
theorem extMk_comp_extClass {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
    {X : C} (R : ProjectiveResolution X) {S : ShortComplex C} (hS : S.ShortExact) {n : ℕ}
    (w : R.complex.X n ⟶ S.X₃) (hw : R.complex.d (n + 1) n ≫ w = 0)
    (w₂ : R.complex.X n ⟶ S.X₂) (hw₂ : w₂ ≫ S.g = w)
    (w₁ : R.complex.X (n + 1) ⟶ S.X₁) (hw₁ : w₁ ≫ S.f = R.complex.d (n + 1) n ≫ w₂)
    (hw₁' : R.complex.d (n + 2) (n + 1) ≫ w₁ = 0) :
    (R.extMk w (n + 1) rfl hw).comp hS.extClass rfl = R.extMk w₁ (n + 2) rfl hw₁' ∨
    (R.extMk w (n + 1) rfl hw).comp hS.extClass rfl = -R.extMk w₁ (n + 2) rfl hw₁' := by
  letI := HasDerivedCategory.standard C
  let S' : ShortComplex (CochainComplex C ℤ) :=
    S.map (HomologicalComplex.single C (ComplexShape.up ℤ) 0)
  have hS' : S'.ShortExact := hS.map_of_exact _
  have hsd : hS.singleδ = DerivedCategory.triangleOfSESδ hS' :=
    ExtConeLift.single_delta_eq_triangleOfSES_delta (C := C) hS
  let cw₂ : Cochain R.cochainComplex S'.X₂ (↑n : ℤ) :=
    Cochain.toSingleMk ((R.cochainComplexXIso (-↑n) n rfl).hom ≫ w₂)
      (show -↑n + (↑n : ℤ) = 0 by simp)
  let ccw : Cocycle R.cochainComplex S'.X₃ (↑n : ℤ) :=
    Cocycle.toSingleMk ((R.cochainComplexXIso (-↑n) n rfl).hom ≫ w) (by simp)
      (-↑(n + 1)) (by lia) (by
        rw [ProjectiveResolution.cochainComplex_d R (-↑(n+1)) (-↑n) (n+1) n rfl rfl]
        simp only [Category.assoc, Iso.inv_hom_id_assoc, hw, Limits.comp_zero])
  let ccw₁ : Cocycle R.cochainComplex S'.X₁ ((↑n : ℤ) + 1) :=
    Cocycle.toSingleMk ((R.cochainComplexXIso (-↑(n+1)) (n+1) rfl).hom ≫ w₁)
      (show -↑(n+1) + ((↑n : ℤ) + 1) = 0 by simp)
      (-↑(n + 2)) (by lia) (by
        rw [ProjectiveResolution.cochainComplex_d R (-↑(n+2)) (-↑(n+1)) (n+2) (n+1) rfl rfl]
        simp only [Category.assoc, Iso.inv_hom_id_assoc, hw₁', Limits.comp_zero])
  have hδ : δ (↑n : ℤ) ((↑n : ℤ) + 1) cw₂ =
      ((((↑n : ℤ) + 1).negOnePow : ℤˣ) : ℤ) • Cochain.toSingleMk
        ((R.cochainComplexXIso (-↑(n + 1)) (n + 1) rfl).hom ≫ (R.complex.d (n + 1) n ≫ w₂))
        (show -↑(n + 1) + ((↑n : ℤ) + 1) = 0 by simp) :=
    ExtConeLift.delta_toSingleMk_eq (R := R) (S := S) w₂
  have hcRaw := ExtConeLift.comp_toSingleMk_eq (R := R) (S := S) w₂ w₁ hw₁
  have hc₁ : ccw₁.1.comp
        (Cochain.ofHom ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map S.f))
        (show ((↑n : ℤ) + 1) + 0 = (↑n : ℤ) + 1 by omega) =
      Cochain.toSingleMk ((R.cochainComplexXIso (-↑(n + 1)) (n + 1) rfl).hom ≫
        (R.complex.d (n + 1) n ≫ w₂)) (show -↑(n + 1) + ((↑n : ℤ) + 1) = 0 by simp) := by
    dsimp only [ccw₁]
    rw [Cocycle.toSingleMk_coe]
    exact hcRaw
  have hneg₁ : ((-ccw₁).1 : Cochain R.cochainComplex S'.X₁ ((↑n : ℤ) + 1)) = -(ccw₁.1) :=
    Cocycle.coe_neg ccw₁
  have hg : S'.g = (CochainComplex.singleFunctor C 0).map S.g := rfl
  have hf : S'.f = (HomologicalComplex.single C (ComplexShape.up ℤ) 0).map S.f := rfl
  have hf₁ : S'.X₁ = (CochainComplex.singleFunctor C 0).obj S.X₁ := rfl
  have hf₃ : S'.X₃ = (CochainComplex.singleFunctor C 0).obj S.X₃ := rfl
  -- the lift of `w` along `S.g`
  have hβ : cw₂.comp (Cochain.ofHom S'.g) (add_zero (↑n : ℤ)) = ccw.1 := by
    rw [hg]
    show (Cochain.toSingleMk ((R.cochainComplexXIso (-↑n) n rfl).hom ≫ w₂)
        (show -↑n + (↑n : ℤ) = 0 by simp)).comp
        (Cochain.ofHom ((CochainComplex.singleFunctor C 0).map S.g)) (add_zero (↑n : ℤ)) =
      Cochain.toSingleMk ((R.cochainComplexXIso (-↑n) n rfl).hom ≫ w) (show -↑n + (↑n : ℤ) = 0 by simp)
    rw [← Cochain.toSingleMk_postcomp
      (f := (R.cochainComplexXIso (-↑n) n rfl).hom ≫ w₂)
      (h := (show -↑n + (↑n : ℤ) = 0 by simp)) (g := S.g)]
    rw [show ((R.cochainComplexXIso (-↑n) n rfl).hom ≫ w₂) ≫ S.g
        = (R.cochainComplexXIso (-↑n) n rfl).hom ≫ w from by
      rw [Category.assoc, hw₂]]
  -- the lifted cocycle post-composed with `descShortComplex` is `ccw`
  have hγ : ∀ (α : Cocycle R.cochainComplex S'.X₁ ((↑n : ℤ) + 1))
      (heq : δ (↑n : ℤ) ((↑n : ℤ) + 1) cw₂ +
        α.1.comp (Cochain.ofHom S'.f) (add_zero ((↑n : ℤ) + 1)) = 0),
      (CochainComplex.mappingCone.liftCocycle S'.f α cw₂ rfl heq).postcomp
        (CochainComplex.mappingCone.descShortComplex S') = ccw := by
    intro α heq
    apply Subtype.ext
    show (CochainComplex.mappingCone.liftCocycle S'.f α cw₂ rfl heq).1.comp
        (Cochain.ofHom (CochainComplex.mappingCone.descShortComplex S'))
        (add_zero (↑n : ℤ)) = ccw.1
    rw [show Cochain.ofHom (CochainComplex.mappingCone.descShortComplex S') =
        Cochain.ofHom (CochainComplex.mappingCone.desc S'.f 0 S'.g (by simp)) from rfl]
    rw [CochainComplex.mappingCone.ofHom_desc]
    rw [CochainComplex.mappingCone.liftCocycle_coe]
    rw [CochainComplex.mappingCone.liftCochain_descCochain]
    simp only [Cochain.comp_zero, zero_add]
    exact hβ
  -- description of `extMk` from Mathlib
  have hL1 : (R.extMk w (n + 1) rfl hw).hom =
      (ShiftedHom.mk₀ 0 rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X ≫
        inv (DerivedCategory.Q.map R.π'))).comp
        ((ShiftedHom.map (Cocycle.equivHomShift.symm ccw) DerivedCategory.Q).comp
          (ShiftedHom.mk₀ 0 rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).inv.app S.X₃))
          (zero_add (↑n : ℤ))) (add_zero (↑n : ℤ)) :=
    ProjectiveResolution.extMk_hom ..
  have hL1' : (R.extMk w₁ (n + 2) rfl hw₁').hom =
      (ShiftedHom.mk₀ 0 rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X ≫
        inv (DerivedCategory.Q.map R.π'))).comp
        ((ShiftedHom.map (Cocycle.equivHomShift.symm ccw₁) DerivedCategory.Q).comp
          (ShiftedHom.mk₀ 0 rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).inv.app S.X₁))
          (zero_add ((↑n : ℤ) + 1))) (add_zero ((↑n : ℤ) + 1)) :=
    ProjectiveResolution.extMk_hom ..
  have hC1' : (R.extMk w₁ (n + 2) rfl hw₁').hom =
      (ShiftedHom.mk₀ 0 rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X ≫
        inv (DerivedCategory.Q.map R.π'))).comp
        (ShiftedHom.map (Cocycle.equivHomShift.symm ccw₁) DerivedCategory.Q)
        (add_zero ((↑n : ℤ) + 1)) := by
    rw [hL1']
    rw [show (ShiftedHom.map (Cocycle.equivHomShift.symm ccw₁) DerivedCategory.Q).comp
          (ShiftedHom.mk₀ 0 rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).inv.app S.X₁))
          (zero_add ((↑n : ℤ) + 1))
        = ShiftedHom.map (Cocycle.equivHomShift.symm ccw₁) DerivedCategory.Q from
      ShiftedHom.comp_mk₀_id ..]
  -- cleaned versions
  -- the connective
  have hkey : ∀ (α : Cocycle R.cochainComplex S'.X₁ ((↑n : ℤ) + 1))
      (heq : δ (↑n : ℤ) ((↑n : ℤ) + 1) cw₂ +
        α.1.comp (Cochain.ofHom S'.f) (add_zero ((↑n : ℤ) + 1)) = 0),
      (ShiftedHom.map (Cocycle.equivHomShift.symm ccw) DerivedCategory.Q).comp
          (DerivedCategory.triangleOfSESδ hS') (show 1 + (↑n : ℤ) = (↑n : ℤ) + 1 by lia) =
        -(ShiftedHom.map (Cocycle.equivHomShift.symm α) DerivedCategory.Q) := by
    intro α heq
    rw [show ShiftedHom.map (Cocycle.equivHomShift.symm ccw) DerivedCategory.Q =
        ShiftedHom.map (Cocycle.equivHomShift.symm
          ((CochainComplex.mappingCone.liftCocycle S'.f α cw₂ rfl heq).postcomp
            (CochainComplex.mappingCone.descShortComplex S'))) DerivedCategory.Q from by
      rw [hγ α heq]]
    exact connecting_eq_lift (C := C) hS' cw₂ α heq
  have hmapneg : Cocycle.equivHomShift.symm (-ccw₁) = -(Cocycle.equivHomShift.symm ccw₁) := by
    rw [eq_neg_iff_add_eq_zero, ← map_add, neg_add_cancel, map_zero]
  have hmapneg' : ShiftedHom.map (Cocycle.equivHomShift.symm (-ccw₁)) DerivedCategory.Q =
      -(ShiftedHom.map (Cocycle.equivHomShift.symm ccw₁) DerivedCategory.Q) := by
    rw [hmapneg, shiftedHom_map_neg]
  -- the shifted-hom identity, stated with the objects of the derived category
  have hmain : ∀ (α : Cocycle R.cochainComplex S'.X₁ ((↑n : ℤ) + 1))
      (heq : δ (↑n : ℤ) ((↑n : ℤ) + 1) cw₂ +
        α.1.comp (Cochain.ofHom S'.f) (add_zero ((↑n : ℤ) + 1)) = 0),
      ((ShiftedHom.mk₀ 0 rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X ≫
            inv (DerivedCategory.Q.map R.π'))).comp
          ((ShiftedHom.map (Cocycle.equivHomShift.symm ccw) DerivedCategory.Q).comp
            (ShiftedHom.mk₀ 0 rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).inv.app S.X₃))
            (zero_add (↑n : ℤ))) (add_zero (↑n : ℤ))).comp
        (DerivedCategory.triangleOfSESδ hS') (show 1 + (↑n : ℤ) = (↑n : ℤ) + 1 by lia) =
      -((ShiftedHom.mk₀ 0 rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X ≫
            inv (DerivedCategory.Q.map R.π'))).comp
        (ShiftedHom.map (Cocycle.equivHomShift.symm α) DerivedCategory.Q)
        (add_zero ((↑n : ℤ) + 1))) := by
    intro α heq
    rw [show (ShiftedHom.map (Cocycle.equivHomShift.symm ccw) DerivedCategory.Q).comp
          (ShiftedHom.mk₀ 0 rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).inv.app S.X₃))
          (zero_add (↑n : ℤ))
        = ShiftedHom.map (Cocycle.equivHomShift.symm ccw) DerivedCategory.Q from
      ShiftedHom.comp_mk₀_id ..]
    have hassoc : ((ShiftedHom.mk₀ 0 rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X ≫
            inv (DerivedCategory.Q.map R.π'))).comp
          (ShiftedHom.map (Cocycle.equivHomShift.symm ccw) DerivedCategory.Q)
          (add_zero (↑n : ℤ))).comp
          (DerivedCategory.triangleOfSESδ hS') (show 1 + (↑n : ℤ) = (↑n : ℤ) + 1 by lia)
        = (ShiftedHom.mk₀ 0 rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X ≫
            inv (DerivedCategory.Q.map R.π'))).comp
            ((ShiftedHom.map (Cocycle.equivHomShift.symm ccw) DerivedCategory.Q).comp
              (DerivedCategory.triangleOfSESδ hS') (show 1 + (↑n : ℤ) = (↑n : ℤ) + 1 by lia))
            (show (↑n : ℤ) + 1 + 0 = (↑n : ℤ) + 1 by lia) :=
      ShiftedHom.comp_assoc
        (α := ShiftedHom.mk₀ 0 rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X ≫
          inv (DerivedCategory.Q.map R.π')))
        (β := ShiftedHom.map (Cocycle.equivHomShift.symm ccw) DerivedCategory.Q)
        (γ := DerivedCategory.triangleOfSESδ hS')
        (h₁₂ := (show (↑n : ℤ) + 0 = (↑n : ℤ) by lia))
        (h₂₃ := (show 1 + (↑n : ℤ) = (↑n : ℤ) + 1 by lia))
        (h := (show 1 + (↑n : ℤ) + 0 = (↑n : ℤ) + 1 by lia))
    have hkey' : (ShiftedHom.mk₀ 0 rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X ≫
            inv (DerivedCategory.Q.map R.π'))).comp
            ((ShiftedHom.map (Cocycle.equivHomShift.symm ccw) DerivedCategory.Q).comp
              (DerivedCategory.triangleOfSESδ hS') (show 1 + (↑n : ℤ) = (↑n : ℤ) + 1 by lia))
            (show (↑n : ℤ) + 1 + 0 = (↑n : ℤ) + 1 by lia)
        = -((ShiftedHom.mk₀ 0 rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X ≫
            inv (DerivedCategory.Q.map R.π'))).comp
            (ShiftedHom.map (Cocycle.equivHomShift.symm α) DerivedCategory.Q)
            (add_zero ((↑n : ℤ) + 1))) := by
      have h1 : (ShiftedHom.mk₀ 0 rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X ≫
              inv (DerivedCategory.Q.map R.π'))).comp
            ((ShiftedHom.map (Cocycle.equivHomShift.symm ccw) DerivedCategory.Q).comp
              (DerivedCategory.triangleOfSESδ hS') (show 1 + (↑n : ℤ) = (↑n : ℤ) + 1 by lia))
            (show (↑n : ℤ) + 1 + 0 = (↑n : ℤ) + 1 by lia)
          = ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X ≫
              inv (DerivedCategory.Q.map R.π')) ≫
            ((ShiftedHom.map (Cocycle.equivHomShift.symm ccw) DerivedCategory.Q).comp
              (DerivedCategory.triangleOfSESδ hS') (show 1 + (↑n : ℤ) = (↑n : ℤ) + 1 by lia)) :=
        ShiftedHom.mk₀_comp 0 rfl
          (((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X ≫
            inv (DerivedCategory.Q.map R.π'))) _
      have h2 : ((ShiftedHom.mk₀ 0 rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X ≫
              inv (DerivedCategory.Q.map R.π'))).comp
            (ShiftedHom.map (Cocycle.equivHomShift.symm α) DerivedCategory.Q)
            (add_zero ((↑n : ℤ) + 1)))
          = ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X ≫
              inv (DerivedCategory.Q.map R.π')) ≫
            ShiftedHom.map (Cocycle.equivHomShift.symm α) DerivedCategory.Q :=
        ShiftedHom.mk₀_comp 0 rfl
          (((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X ≫
            inv (DerivedCategory.Q.map R.π'))) _
      rw [h1, h2]
      rw [congrArg (fun (Y : DerivedCategory.Q.obj R.cochainComplex ⟶
                    (DerivedCategory.Q.obj S'.X₁)⟦((↑n : ℤ) + 1)⟧) =>
              ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X ≫
                inv (DerivedCategory.Q.map R.π')) ≫ Y) (hkey α heq)]
      rw [Preadditive.comp_neg]
    exact hassoc.trans hkey'
  rcases Int.units_eq_one_or (((↑n : ℤ) + 1).negOnePow) with hs | hs
  · left
    have heq : δ (↑n : ℤ) ((↑n : ℤ) + 1) cw₂ +
        (-ccw₁).1.comp (Cochain.ofHom S'.f) (add_zero ((↑n : ℤ) + 1)) = 0 := by
      rw [hf]
      rw [hδ, hs]
      simp only [Units.val_one, one_smul]
      rw [hneg₁]
      rw [Cochain.neg_comp, ← hc₁]
      exact add_neg_cancel _
    have hfin : -((ShiftedHom.mk₀ 0 rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X ≫
          inv (DerivedCategory.Q.map R.π'))).comp
        (ShiftedHom.map (Cocycle.equivHomShift.symm (-ccw₁)) DerivedCategory.Q)
        (add_zero ((↑n : ℤ) + 1))) = (R.extMk w₁ (n + 2) rfl hw₁').hom := by
      rw [hmapneg']
      rw [show (ShiftedHom.mk₀ 0 rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X ≫
            inv (DerivedCategory.Q.map R.π'))).comp
          (-(ShiftedHom.map (Cocycle.equivHomShift.symm ccw₁) DerivedCategory.Q))
          (add_zero ((↑n : ℤ) + 1)) =
        -((ShiftedHom.mk₀ 0 rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X ≫
            inv (DerivedCategory.Q.map R.π'))).comp
          (ShiftedHom.map (Cocycle.equivHomShift.symm ccw₁) DerivedCategory.Q)
          (add_zero ((↑n : ℤ) + 1))) from
        ShiftedHom.comp_neg (ShiftedHom.mk₀ 0 rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X ≫
          inv (DerivedCategory.Q.map R.π')))
          (ShiftedHom.map (Cocycle.equivHomShift.symm ccw₁) DerivedCategory.Q)
          (add_zero ((↑n : ℤ) + 1))]
      rw [neg_neg, ← hC1']
    apply Abelian.Ext.ext
    rw [Abelian.Ext.comp_hom]
    rw [hL1, ShortComplex.ShortExact.extClass_hom, hsd]
    exact (hmain (-ccw₁) heq).trans hfin
  · right
    have heq : δ (↑n : ℤ) ((↑n : ℤ) + 1) cw₂ +
        ccw₁.1.comp (Cochain.ofHom S'.f) (add_zero ((↑n : ℤ) + 1)) = 0 := by
      rw [hf]
      rw [hδ, hs]
      simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_smul]
      dsimp only [ccw₁]
      rw [Cocycle.toSingleMk_coe, ← hc₁]
      exact neg_add_cancel _
    have hfin : -((ShiftedHom.mk₀ 0 rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X ≫
          inv (DerivedCategory.Q.map R.π'))).comp
        (ShiftedHom.map (Cocycle.equivHomShift.symm ccw₁) DerivedCategory.Q)
        (add_zero ((↑n : ℤ) + 1))) = -(R.extMk w₁ (n + 2) rfl hw₁').hom :=
      congrArg Neg.neg hC1'.symm
    apply Abelian.Ext.ext
    rw [Abelian.Ext.neg_hom]
    rw [Abelian.Ext.comp_hom]
    rw [hL1, ShortComplex.ShortExact.extClass_hom, hsd]
    exact (hmain ccw₁ heq).trans hfin

end Work.SSGRoute
