import Mathlib
import Submission.Work.DSF1.Sheaf.Beta

namespace Work.DSF1.Sheaf

open CategoryTheory AlgebraicGeometry Opposite Limits TopologicalSpace

set_option maxHeartbeats 4000000

universe u

-- `betaGen V V' g` is the canonical structure map
-- `𝒪_V ⟶ g_* 𝒪_{V'}` associated with a morphism `g : V' ⟶ V` of open subschemes:
-- it is `SheafOfModules.unitToPushforwardObjUnit`.
set_option backward.isDefEq.respectTransparency false in
theorem betaGen_eq {X : Scheme.{u}} {V V' : X.Opens} (g : V'.toScheme ⟶ V.toScheme) :
    Work.DSF1.Sheaf.betaGen V V' g =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom := by
  apply ((Scheme.Modules.pushforward g).obj
    (SheafOfModules.unit (V'.toScheme.ringCatSheaf))).unitHomEquiv.injective
  rw [Work.DSF1.Sheaf.betaGen, Equiv.apply_symm_apply]
  rw [show Work.DSF1.Sheaf.betaSect V V' g =
      SheafOfModules.pushforwardSections g.toRingCatSheafHom
        ((SheafOfModules.unit (V'.toScheme.ringCatSheaf)).unitHomEquiv (𝟙 _)) from rfl,
    SheafOfModules.pushforwardSections_unitHomEquiv]
  congr 1

-- The value of `betaGen` on sections is the ring map induced by the morphism.
set_option backward.isDefEq.respectTransparency false in
theorem betaGen_app_sec {X : Scheme.{u}} {V V' : X.Opens}
    (g : V'.toScheme ⟶ V.toScheme) (U : V.toScheme.Opens) (a : Γ(V.toScheme, U)) :
    (Scheme.Modules.Hom.app (Work.DSF1.Sheaf.betaGen V V' g) U) a = g.app U a := by
  rw [betaGen_eq]
  change (ConcreteCategory.hom ((SheafOfModules.unitToPushforwardObjUnit
      (Scheme.Hom.toRingCatSheafHom g)).val.app (op U))) a =
    (ConcreteCategory.hom (Scheme.Hom.app g U)) a
  exact SheafOfModules.unitToPushforwardObjUnit_val_app_apply (Scheme.Hom.toRingCatSheafHom g) a

-- `(V'.ι)_* 𝒪_{V'}` is the restriction of `𝒪_X` along `V'.ι`, so its presheaf of
-- sections is computed by `X.presheaf`.
lemma concreteHom_presheaf_unit_X {X : Scheme.{u}} (V' : X.Opens)
    {A B : (V'.toScheme).Opens} (i : A ⟶ B) (y : Γ(V', B)) :
    ConcreteCategory.hom ((V'.toScheme).presheaf.map i.op) y
      = ConcreteCategory.hom (X.presheaf.map (V'.ι.opensFunctor.map i).op) y := by
  rw [Scheme.Opens.toScheme_presheaf_map, Quiver.Hom.unop_op]
  rfl

-- The reindexing appearing in `pushforwardCongr`, expressed inside `X.presheaf`.
lemma restr_R {X : Scheme.{u}} (V' : X.Opens)
    {A B : (V'.toScheme).Opens} (i : A ⟶ B) (y : Γ(V', B)) :
    ConcreteCategory.hom ((Scheme.Modules.presheaf
      (SheafOfModules.unit (V'.toScheme.ringCatSheaf))).map i.op) y
      = ConcreteCategory.hom (X.presheaf.map (V'.ι.opensFunctor.map i).op) y := by
  rw [show ConcreteCategory.hom ((Scheme.Modules.presheaf
        (SheafOfModules.unit (V'.toScheme.ringCatSheaf))).map i.op) y
      = ConcreteCategory.hom ((V'.toScheme).presheaf.map i.op) y from rfl,
    concreteHom_presheaf_unit_X]

-- The restriction map `restr h` of the Čech presheaf, evaluated on sections: it is
-- the corresponding restriction map of the structure sheaf of `X`.
set_option backward.isDefEq.respectTransparency false in
theorem restr_app {X : Scheme.{u}} {V V' : X.Opens} (h : V' ≤ V) (W : X.Opens)
    (p : V'.ι ''ᵁ (V'.ι ⁻¹ᵁ W) ≤ V.ι ''ᵁ (V.ι ⁻¹ᵁ W))
    (x : X.presheaf.obj (Opposite.op (V.ι ''ᵁ (V.ι ⁻¹ᵁ W)))) :
    (Work.DSF1.Sheaf.restr h).app W x = X.presheaf.map (homOfLE p).op x := by
  unfold Work.DSF1.Sheaf.restr
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.pushforwardCongr_hom_app_app]
  rw [AddCommGrpCat.comp_apply]
  have hP : (ConcreteCategory.hom (Scheme.Modules.Hom.app
        (Work.DSF1.Sheaf.betaGen V V' (X.homOfLE h)) (V.ι ⁻¹ᵁ W))) x
      = (ConcreteCategory.hom ((X.homOfLE h).app (V.ι ⁻¹ᵁ W))) x :=
    betaGen_app_sec (X.homOfLE h) (V.ι ⁻¹ᵁ W) x
  erw [hP]
  have hQ : (ConcreteCategory.hom ((X.homOfLE h).app (V.ι ⁻¹ᵁ W))) x
      = (ConcreteCategory.hom (X.presheaf.map (homOfLE
          (X.ι_image_homOfLE_le_ι_image h (V.ι ⁻¹ᵁ W))).op)) x := by
    rw [Scheme.homOfLE_app]
    rfl
  erw [hQ]
  have hR := restr_R V'
    (eqToHom (congrArg (fun (m : V'.toScheme ⟶ X) =>
      (TopologicalSpace.Opens.map m.base).obj W) (Scheme.homOfLE_ι X h).symm))
    ((ConcreteCategory.hom (X.presheaf.map (homOfLE
      (X.ι_image_homOfLE_le_ι_image h (V.ι ⁻¹ᵁ W))).op)) x)
  erw [hR]
  erw [← CategoryTheory.comp_apply]
  rw [← Functor.map_comp]
  congr 1

-- The restriction maps of the Čech presheaf are transitive.
set_option backward.isDefEq.respectTransparency false in
theorem restr_trans (X : AlgebraicGeometry.Scheme.{u}) {V V' V'' : X.Opens}
    (h₁ : V' ≤ V) (h₂ : V'' ≤ V') :
    CategoryTheory.CategoryStruct.comp (Work.DSF1.Sheaf.restr h₁) (Work.DSF1.Sheaf.restr h₂) =
      Work.DSF1.Sheaf.restr (h₂.trans h₁) := by
  ext W x
  rw [Scheme.Modules.Hom.comp_app, AddCommGrpCat.comp_apply]
  have p₁ : V'.ι ''ᵁ (V'.ι ⁻¹ᵁ W) ≤ V.ι ''ᵁ (V.ι ⁻¹ᵁ W) := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_le_inf_right W h₁
  have p₂ : V''.ι ''ᵁ (V''.ι ⁻¹ᵁ W) ≤ V'.ι ''ᵁ (V'.ι ⁻¹ᵁ W) := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_le_inf_right W h₂
  have p₃ : V''.ι ''ᵁ (V''.ι ⁻¹ᵁ W) ≤ V.ι ''ᵁ (V.ι ⁻¹ᵁ W) := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_le_inf_right W (h₂.trans h₁)
  have ha1 : (Work.DSF1.Sheaf.restr h₁).app W x = X.presheaf.map (homOfLE p₁).op x :=
    restr_app h₁ W p₁ x
  rw [ha1]
  have ha2 : (Work.DSF1.Sheaf.restr h₂).app W (X.presheaf.map (homOfLE p₁).op x)
      = X.presheaf.map (homOfLE p₂).op (X.presheaf.map (homOfLE p₁).op x) :=
    restr_app h₂ W p₂ (X.presheaf.map (homOfLE p₁).op x)
  erw [ha2]
  have ha3 : (Work.DSF1.Sheaf.restr (h₂.trans h₁)).app W x
      = X.presheaf.map (homOfLE p₃).op x :=
    restr_app (h₂.trans h₁) W p₃ x
  rw [ha3]
  erw [← CategoryTheory.comp_apply]
  rw [← Functor.map_comp]
  congr 1

end Work.DSF1.Sheaf
