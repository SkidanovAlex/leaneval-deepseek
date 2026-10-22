import Mathlib
import Submission.Work.ANALYTIC.PrTop
import Submission.Work.ANALYTIC.MuT
import Submission.Work.ANALYTIC.Final

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

noncomputable section

namespace Work.ANALYTIC

open _root_.LightCondensed _root_.LightCondensed.Solid

/-- `dFree` bundled as a functor; `Submission.Blueprint.dFree f = dFreeF.map f` holds
definitionally. -/
noncomputable abbrev dFreeF : TopCat.{0} ⥤ DLightCondAb :=
  freeLightCondAbOfTopFunctor ⋙ DerivedCategory.singleFunctor LightCondAb 0

/-- `dFree` preserves composition. -/
lemma dFree_comp {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Submission.Blueprint.dFree (f ≫ g) =
      Submission.Blueprint.dFree f ≫ Submission.Blueprint.dFree g :=
  Functor.map_comp dFreeF f g

/-- `dFree` preserves identities. -/
lemma dFree_id (X : TopCat.{0}) :
    Submission.Blueprint.dFree (𝟙 X) = 𝟙 (dFreeF.obj X) :=
  CategoryTheory.Functor.map_id dFreeF X

/-- **Reduction of `HIProp` to the projection form.**  If for every Hausdorff `Y` the projection
`pr : Y × [0,1] ⟶ Y` induces a solid-equivalence `ℤ[Y × [0,1]] ⟶ ℤ[Y]`, then `HIProp` holds, i.e.
the inclusion `i₀` (at `t = 0`) is a solid-equivalence.

Route: `Submission.Blueprint.i₀ Y ≫ prTop Y = 𝟙 Y` (`Work.ANALYTIC.i₀_prTop`), so by functoriality
of `dFree`, `dFree (i₀ Y) ≫ dFree (prTop Y) = dFree (𝟙 Y)`, which is an isomorphism
(`Submission.Blueprint.ToolkitProp.of_iso` applied to the iso arising from `dFree` on identities);
`Submission.Blueprint.ToolkitProp.of_comp_right` then gives `SolidEquiv (dFree (i₀ Y))` from
`SolidEquiv (dFree (prTop Y))`.  `ToolkitProp` is proved in area TOOLKIT
(`Work.ANALYTIC.toolkitProp`, `Submission.Work.ANALYTIC.MuT`). -/
theorem hi_prop_of_proj
    (h : ∀ (Y : TopCat.{0}) [T2Space Y],
      Submission.Blueprint.SolidEquiv (Submission.Blueprint.dFree (prTop Y))) :
    Submission.Blueprint.HIProp := by
  intro Y hY
  haveI : T2Space Y := hY
  -- `dFree (i₀ Y)` has the one-sided inverse `dFree (prTop Y)`, and the composite is the
  -- image of the identity, hence an isomorphism.
  have hcomp : Submission.Blueprint.dFree (Submission.Blueprint.i₀ Y) ≫
      Submission.Blueprint.dFree (prTop Y) = 𝟙 (dFreeF.obj Y) := by
    rw [← dFree_comp, i₀_prTop, dFree_id]
  exact toolkitProp.of_comp_right _ _ (h Y)
    (by rw [hcomp]; exact toolkitProp.of_iso _ (IsIso.id _))

end Work.ANALYTIC

/-- Convenience alias: the statement of `Work.ANALYTIC.Work.ANALYTIC.hi_prop_of_proj` under the
short name `Work.ANALYTIC.hi_prop_of_proj`, for callers that refer to this module's declaration by
the requested name. -/
theorem hi_prop_of_proj
    (h : ∀ (Y : TopCat.{0}) [T2Space Y],
      Submission.Blueprint.SolidEquiv (Submission.Blueprint.dFree (prTop Y))) :
    Submission.Blueprint.HIProp :=
  _root_.Work.ANALYTIC.Work.ANALYTIC.hi_prop_of_proj h
