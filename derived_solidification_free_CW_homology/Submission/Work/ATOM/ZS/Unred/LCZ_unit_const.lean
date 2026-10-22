import Mathlib

open CategoryTheory CategoryTheory.Limits LightCondensed LightProfinite Opposite

/-!
# The unit of the locally-constant adjunction at a point

We prove that the unit of the adjunction
`LightCondMod.LocallyConstant.adjunction R : functor R ⊣ underlying (ModuleCat R)`
at a module `M` (evaluated at a point) is the canonical identification
`M ≅ ↧(LocallyConstant (*) M)`, i.e. it sends `x : M` to the constant map with value `x`.

The adjunction `LightCondMod.LocallyConstant.adjunction R` is obtained by transporting
`LightCondensed.discreteUnderlyingAdj` along the natural isomorphism
`functorIsoDiscrete R`, so its unit is
`adj.unit.app M ≫ H.map (iso.hom.app M)`, and `iso.hom.app M` unfolds to
`discrete.map (aux₁.hom) ≫ adj.counit.app (F.obj M)` where `aux₁` is
`LightCondMod.LocallyConstant.functorIsoDiscreteAux₁` (the identification `M ≅ ↧(LocallyConstant (*) M)`).
The unit naturality of `adj` applied to `aux₁.hom`, together with the right triangle identity of
`adj` at `F.obj M`, then shows that everything collapses to `aux₁.hom`.
-/

namespace Work.ATOM.ZS.Unred

/-- The identification `M ≅ ↧(LocallyConstant ↥* M)` of `LightCondMod.LocallyConstant.functorIsoDiscreteAux₁`,
with its codomain written as the value at the point of the locally constant `M`-sheaf. Writing it as
an opaque constant with this type keeps all the (definitionally equal) type ascriptions aligned. -/
noncomputable def LCZauxHom (M : ModuleCat ℤ) :
    M ⟶ (LightCondensed.underlying (ModuleCat ℤ)).obj
      ((LightCondMod.LocallyConstant.functor ℤ).obj M) :=
  (LightCondMod.LocallyConstant.functorIsoDiscreteAux₁ ℤ M).hom

/-- The unit of an adjunction transported along a natural isomorphism on the left. -/
lemma ofNatIsoLeft_unit_app {C D' : Type*} [Category C] [Category D']
    {F₀ G₀ : C ⥤ D'} {H₀ : D' ⥤ C} (adj₀ : F₀ ⊣ H₀) (iso : F₀ ≅ G₀) (X : C) :
    ((Adjunction.ofNatIsoLeft adj₀ iso).unit.app X) = adj₀.unit.app X ≫ H₀.map (iso.hom.app X) :=
  rfl

/-- The component of `functorIsoDiscrete` with the adjunction's own counit made explicit. -/
lemma functorIsoDiscrete_inv_app (M : ModuleCat ℤ) :
    (LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).inv.app M
      = (LightCondMod.LocallyConstant.functorIsoDiscreteComponents ℤ M).hom := by
  have h : LightCondMod.LocallyConstant.functorIsoDiscrete ℤ =
      NatIso.ofComponents
        (fun M ↦ (LightCondMod.LocallyConstant.functorIsoDiscreteComponents ℤ M).symm) _ := rfl
  rw [h]
  exact NatIso.ofComponents_inv_app _ _ _

/-- `functorIsoDiscreteComponents` is the composite of `functorIsoDiscreteAux₂` with the counit. -/
lemma functorIsoDiscreteComponents_hom_eq (M : ModuleCat ℤ) :
    (LightCondMod.LocallyConstant.functorIsoDiscreteComponents ℤ M).hom
      = (LightCondensed.discrete (ModuleCat ℤ)).map (LCZauxHom M)
        ≫ (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).counit.app
            ((LightCondMod.LocallyConstant.functor ℤ).obj M) :=
  rfl

/-- **The unit of the locally constant adjunction is the canonical identification
`M ≅ ↧(LocallyConstant (*) M)`.** -/
lemma LCZ_unit_eq_auxHom (M : ModuleCat ℤ) :
    (LightCondMod.LocallyConstant.adjunction ℤ).unit.app M = LCZauxHom M := by
  dsimp only [LightCondMod.LocallyConstant.adjunction]
  rw [ofNatIsoLeft_unit_app]
  rw [show ((LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).symm).hom.app M
      = (LightCondMod.LocallyConstant.functorIsoDiscreteComponents ℤ M).hom
      from functorIsoDiscrete_inv_app M]
  rw [functorIsoDiscreteComponents_hom_eq]
  rw [show (LightCondensed.underlying (ModuleCat ℤ)).map
        ((LightCondensed.discrete (ModuleCat ℤ)).map (LCZauxHom M)
          ≫ (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).counit.app
              ((LightCondMod.LocallyConstant.functor ℤ).obj M))
      = (LightCondensed.underlying (ModuleCat ℤ)).map
          ((LightCondensed.discrete (ModuleCat ℤ)).map (LCZauxHom M))
        ≫ (LightCondensed.underlying (ModuleCat ℤ)).map
            ((LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).counit.app
              ((LightCondMod.LocallyConstant.functor ℤ).obj M)) from rfl]
  rw [← Category.assoc]
  have hnat := (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).unit_naturality
    (f := LCZauxHom M)
  rw [hnat]
  rw [Category.assoc]
  have htri := (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).right_triangle_components
    ((LightCondMod.LocallyConstant.functor ℤ).obj M)
  rw [htri, Category.comp_id]

/-- The value of `LCZauxHom` on an element: the constant map. -/
lemma LCZauxHom_apply (M : ModuleCat ℤ) (x : M) :
    (((LightCondMod.LocallyConstant.functorIsoDiscreteAux₁ ℤ M).hom) x)
      = LocallyConstant.const (↥(LightProfinite.of PUnit.{1}).toTop) x := by
  dsimp only [LightCondMod.LocallyConstant.functorIsoDiscreteAux₁]
  simp only [ConcreteCategory.hom_ofHom]
  rfl

theorem LCZ_unit_const (M : ModuleCat ℤ) (x : M) : ((LightCondMod.LocallyConstant.adjunction ℤ).unit.app M) x = LocallyConstant.const (↥(LightProfinite.of PUnit.{1}).toTop) x := by
  rw [LCZ_unit_eq_auxHom]
  exact LCZauxHom_apply M x

end Work.ATOM.ZS.Unred
