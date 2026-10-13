import Mathlib
import Submission.Work.DSMap.Map
import Submission.Work.DSF1.Modules.pushforward_unit_sections
import Submission.Work.DSF1.Sheaf.CechSheaf

/-!
# The restriction maps of the Čech presheaf of the structure sheaf

For a scheme `X` and a morphism `g : V'.toScheme ⟶ V.toScheme` between open subschemes,
the pushforward `g_* 𝒪_{V'}` is an `𝒪_V`-module.  The canonical `𝒪_V`-linear map
`𝒪_V ⟶ g_* 𝒪_{V'}` is the structure map induced by `g`; it is classified, via
`SheafOfModules.unitHomEquiv`, by the section of `g_* 𝒪_{V'}` which is constantly `1`.

Pushing further along `V.ι` gives the restriction map
`(V.ι)_* 𝒪_V ⟶ (V'.ι)_* 𝒪_{V'}` of the Čech presheaf `V ↦ (V.ι)_* 𝒪_V`.
-/

namespace Work.DSF1.Sheaf

universe u

open CategoryTheory AlgebraicGeometry Opposite Limits TopologicalSpace

/-- The section of `g_* 𝒪_{V'}` which is constantly `1`. -/
noncomputable def betaSect {X : Scheme.{u}} (V V' : X.Opens)
    (g : V'.toScheme ⟶ V.toScheme) :
    ((Scheme.Modules.pushforward g).obj
      (SheafOfModules.unit V'.toScheme.ringCatSheaf)).sections :=
  let s := (SheafOfModules.unit V'.toScheme.ringCatSheaf).unitHomEquiv (𝟙 _)
  PresheafOfModules.sectionsMk (fun W => s.val (Opposite.op (g ⁻¹ᵁ W.unop)))
    (by intro W W' i; exact s.property ((Opens.map g.base).map i.unop).op)

/-- The canonical `𝒪_V`-linear map `𝒪_V ⟶ g_* 𝒪_{V'}`; it is the structure morphism of the
pushforward, i.e. the ring map `g` itself. -/
noncomputable def betaGen {X : Scheme.{u}} (V V' : X.Opens)
    (g : V'.toScheme ⟶ V.toScheme) :
    SheafOfModules.unit V.toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pushforward g).obj (SheafOfModules.unit V'.toScheme.ringCatSheaf) :=
  ((Scheme.Modules.pushforward g).obj
      (SheafOfModules.unit V'.toScheme.ringCatSheaf)).unitHomEquiv.symm (betaSect V V' g)

/-- The restriction `(V.ι)_* 𝒪_V ⟶ (V'.ι)_* 𝒪_{V'}` for `h : V' ≤ V`. -/
noncomputable def restr {X : Scheme.{u}} {V V' : X.Opens} (h : V' ≤ V) :
    Work.DSF1.secSheaf V ⟶ Work.DSF1.secSheaf V' :=
  (Scheme.Modules.pushforward V.ι).map (betaGen V V' (X.homOfLE h)) ≫
    (Scheme.Modules.pushforwardCongr (Scheme.homOfLE_ι X h)).hom.app
      (SheafOfModules.unit V'.toScheme.ringCatSheaf)

end Work.DSF1.Sheaf
