import Submission.Blueprint.Interfaces

/-!
# AREA FLAT — setup

Free light condensed abelian groups `ℤ[T]` are flat.  This file fixes the conventions and the
basic dictionary on which the rest of the area is built.

## Conventions

* `siteJ` is the coherent topology on light profinite sets; the category of presheaves of
  abelian groups is `PreMod`, and `sheafify ⊣ presheafOf` is the sheafification adjunction
  between `PreMod` and `LightCondAb = LightCondMod ℤ`.
* `LightCondAb` carries the monoidal structure of `Mathlib.Condensed.Light.Monoidal`: it is the
  localization of the *sectionwise* (Day) tensor product of presheaves along sheafification.
* `sectionwiseFree T` is the presheaf `S ↦ ℤ[T(S)]`.  Its sheafification is `ℤ[T] = free ℤ T`
  (`free_eq_sheafify_sectionwiseFree`); this is the definitional unfolding of `LightCondensed.free`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

namespace Work.FLAT

/-- The coherent Grothendieck topology on light profinite sets. -/
abbrev siteJ : GrothendieckTopology LightProfinite.{0} := coherentTopology LightProfinite.{0}

/-- Presheaves of abelian groups on light profinite sets. -/
abbrev PreMod : Type 1 := (LightProfinite.{0})ᵒᵖ ⥤ ModuleCat.{0} ℤ

/-- The sheafification functor `PreMod ⥤ LightCondAb`. -/
noncomputable abbrev sheafify : PreMod ⥤ LightCondAb := presheafToSheaf siteJ (ModuleCat.{0} ℤ)

/-- The functor sending a light condensed abelian group to its underlying presheaf. -/
noncomputable abbrev presheafOf : LightCondAb ⥤ PreMod := sheafToPresheaf siteJ (ModuleCat.{0} ℤ)

/-- The **sectionwise free presheaf** on a light condensed set `T`: the presheaf
`S ↦ ℤ[T(S)]`.  It is sectionwise a free `ℤ`-module, hence sectionwise flat. -/
noncomputable def sectionwiseFree (T : LightCondSet) : PreMod := T.obj ⋙ ModuleCat.free ℤ

lemma sectionwiseFree_obj (T : LightCondSet) (S : (LightProfinite.{0})ᵒᵖ) :
    (sectionwiseFree T).obj S = (ModuleCat.free (R := ℤ)).obj (T.obj.obj S) := rfl

/-- The sections of the sectionwise free presheaf are free, hence flat, `ℤ`-modules. -/
lemma sectionwiseFree_flat (T : LightCondSet) (S : (LightProfinite.{0})ᵒᵖ) :
    Module.Flat ℤ ((sectionwiseFree T).obj S) := by
  change Module.Flat ℤ ((T.obj.obj S) →₀ ℤ)
  infer_instance

/-- `ℤ[T]` is, by definition, the sheafification of the sectionwise free presheaf on `T`. -/
lemma free_eq_sheafify_sectionwiseFree (T : LightCondSet) :
    (LightCondensed.free (R := ℤ)).obj T = sheafify.obj (sectionwiseFree T) := rfl

/-- The counit of the sheafification adjunction is an isomorphism: sheafifying a sheaf gives it
back (up to the canonical isomorphism). -/
lemma isIso_sheafification_counit : IsIso (sheafificationAdjunction siteJ (ModuleCat.{0} ℤ)).counit :=
  inferInstance

/-- The canonical isomorphism `Z ≅ L(S Z)` for a light condensed abelian group `Z`: the inverse
of the counit of the sheafification adjunction. -/
noncomputable def sheafifyCounitIso (Z : LightCondAb) :
    Z ≅ sheafify.obj (presheafOf.obj Z) :=
  (asIso (sheafificationAdjunction siteJ (ModuleCat.{0} ℤ)).counit).symm.app Z

end Work.FLAT
