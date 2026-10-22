import Mathlib
import Submission.Work.CWIND.Basic

/-!
# CWIND/T8 — definitions for the Mayer–Vietoris step of the CW induction

This file collects the definitions used in `Work.CWIND.GClass.G_mv` (the `mv` field of the
class `GOf b`), so that they can be shared with the auxiliary lemmas.

* `GG` is the functor "apply the discrete light condensed abelian group functor and then extend
  by zero" from `ℕ`-graded chain complexes of abelian groups to cochain complexes of light
  condensed abelian groups.  It is the functor through which the singular-chain Mayer–Vietoris
  theorem (`SingMVProp`, a statement about plain chain complexes) is transported to the light
  condensed world.
* `Cfun` is the singular chain complex of a space viewed as a cochain complex of light condensed
  abelian groups (that is, `singularChainsLightCondAbComplexFunctor`), and `Zfun` is `ℤ[-]`
  concentrated in degree `0`.
-/

noncomputable section

namespace Work.CWIND.GClass

open CategoryTheory CategoryTheory.Limits LightCondensed LightProfinite
open LightCondensed.Solid Submission.Blueprint

/-- The functor from `ℕ`-graded chain complexes of `ℤ`-modules to cochain complexes of light
condensed abelian groups which applies the discrete (constant sheaf) functor degreewise and then
extends by zero, placing chain degree `n` in cochain degree `-n`. -/
abbrev GG : ChainComplex (ModuleCat.{0} ℤ) ℕ ⥤ CochainComplex LightCondAb ℤ :=
  (LightCondensed.discrete (ModuleCat ℤ)).mapHomologicalComplex (ComplexShape.down ℕ) ⋙
    ComplexShape.embeddingDownNat.extendFunctor LightCondAb

/-- The singular chain complex of a topological space, as a cochain complex of light condensed
abelian groups.  This is definitionally `singularChainsLightCondAbComplexFunctor`. -/
abbrev Cfun : TopCat.{0} ⥤ CochainComplex LightCondAb ℤ := singC ⋙ GG

/-- `ℤ[-]` concentrated in cochain degree `0`. -/
abbrev Zfun : TopCat.{0} ⥤ CochainComplex LightCondAb ℤ :=
  freeLightCondAbOfTopFunctor ⋙ CochainComplex.singleFunctor LightCondAb 0

@[simp]
lemma Cfun_eq : Cfun = singularChainsLightCondAbComplexFunctor := rfl

end Work.CWIND.GClass
