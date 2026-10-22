/-
AREA RESOL — small coproducts of light condensed abelian groups, as instances.

Mathlib knows that `LightCondAb = Sheaf (coherentTopology LightProfinite) (ModuleCat ℤ)` has
all small colimits, but instance search for `HasColimit (Discrete.functor M)` (equivalently
`HasCoproduct M`) for `M : J → LightCondAb` times out, because the unification has to unfold
`LightCondMod`, `LightCondensed` and the `SmallModel` machinery of the essentially small
site.  The instances below are stated *directly* in terms of `LightCondAb`, so that they are
found immediately; they are the same instances as the ones in Mathlib for sheaves
(`Sheaf.instHasColimitsOfShape` uses `Sheaf.sheafifyCocone` and
`Sheaf.isColimitSheafifyCocone`).

We also record the consequences we need in the rest of the area:
* `HasColimitsOfShape (Discrete J) LightCondAb` (all small coproducts);
* `HasSheafify` for the coherent topology on light profinite sets with values in `ℤ`-modules;
* `HasExactColimitsOfShape (Discrete J) LightCondAb`, i.e. Grothendieck's AB4: small
  coproducts in `LightCondAb` are exact.  This is the instance
  `Sheaf.hasExactColimitsOfShape` for sheaves, using that coproducts of `ℤ`-modules are exact.
-/
import Mathlib
import Submission.Work.RESOL.Basic

open CategoryTheory Limits LightProfinite LightCondensed

noncomputable section

namespace Work.RESOL

/-- Small coproducts in light condensed abelian groups: the coproduct of a family of light
condensed abelian groups is the sheafification of the sectionwise coproduct. -/
instance hasCoproductLightCondAb (J : Type) (M : J → LightCondAb) : HasCoproduct M :=
  ⟨⟨Sheaf.sheafifyCocone
      (colimit.cocone (Discrete.functor M ⋙ CategoryTheory.sheafToPresheaf
        (coherentTopology LightProfinite.{0}) (ModuleCat.{0} ℤ))),
    Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩⟩

/-- Light condensed abelian groups have all small coproducts. -/
instance hasColimitsOfShapeLightCondAb (J : Type) : HasColimitsOfShape (Discrete J) LightCondAb :=
  ⟨fun F => HasColimit.mk
    ⟨Sheaf.sheafifyCocone
        (colimit.cocone (F ⋙ CategoryTheory.sheafToPresheaf
          (coherentTopology LightProfinite.{0}) (ModuleCat.{0} ℤ))),
      Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩⟩

/-- The coherent topology on light profinite sets has a sheafification functor with values in
`ℤ`-modules (an instance of `LightProfinite.hasSheafify`). -/
instance hasSheafifyCoherentLightProfinite :
    HasSheafify (coherentTopology LightProfinite.{0}) (ModuleCat.{0} ℤ) :=
  LightProfinite.hasSheafify (ModuleCat.{0} ℤ)

/-- Grothendieck's AB4 for light condensed abelian groups: small coproducts are exact. -/
instance hasExactColimitsOfShapeLightCondAb (J : Type) :
    HasExactColimitsOfShape (Discrete J) LightCondAb :=
  Sheaf.hasExactColimitsOfShape (K := Discrete J) (J := coherentTopology LightProfinite.{0})

end Work.RESOL
