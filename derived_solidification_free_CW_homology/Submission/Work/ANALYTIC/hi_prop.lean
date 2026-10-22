import Mathlib
import Submission.Work.ANALYTIC.profinite_HI
import Submission.Work.ANALYTIC.PrTop
import Submission.Work.ANALYTIC.MuT
import Submission.Work.ANALYTIC.Final
import Submission.Work.ANALYTIC.hi_prop_of_proj
import Submission.Work.ANALYTIC.HIAssembly

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

noncomputable section

namespace Work.ANALYTIC

open _root_.LightCondensed _root_.LightCondensed.Solid

/-- **The projection form of homotopy invariance (AN6, REFS/04 §3).**  For every Hausdorff space
`Y`, the projection `pr : Y × [0,1] ⟶ Y` induces a solid-equivalence `ℤ[Y × [0,1]] ⟶ ℤ[Y]`.

This is `Work.ANALYTIC.proj_solidEquiv'` (`Submission/Work/ANALYTIC/HIAssembly.lean`), the Čech
route of REFS/04 §3. -/
theorem proj_solidEquiv_leaf (Y : TopCat.{0}) [T2Space Y] :
    Submission.Blueprint.SolidEquiv (Submission.Blueprint.dFree (Work.ANALYTIC.prTop Y)) :=
  _root_.Work.ANALYTIC.proj_solidEquiv' Y

/-- **AREA ANALYTIC — the deliverable (REFS/04 §3).**  For every Hausdorff space `Y`, the inclusion
`i₀ : Y ⟶ Y × [0,1]` (at `t = 0`) induces a solid-equivalence `ℤ[Y] ⟶ ℤ[Y × [0,1]]`, i.e.
`Submission.Blueprint.HIProp`.

Route (REFS/04 §3):
1. It suffices to prove the statement with the *projection* `prTop Y` in place of `i₀ Y`: since
   `Submission.Blueprint.i₀ Y ≫ prTop Y = 𝟙 Y` (`Work.ANALYTIC.i₀_prTop`), functoriality of `dFree`
   gives `dFree (i₀ Y) ≫ dFree (prTop Y) = dFree (𝟙 Y)`, and `Submission.Blueprint.ToolkitProp`
   (`Work.ANALYTIC.toolkitProp`) gives `SolidEquiv (dFree (i₀ Y))` from `SolidEquiv (dFree (prTop Y))`
   via `of_comp_right` and `of_iso`.  This reduction is `Work.ANALYTIC.hi_prop_of_proj`.
2. For the projection form one takes the sectionwise-split epimorphism
   `covMap Y : cov Y ⟶ Y` of REFS/04 §3 (`Work.ANALYTIC.covMap`, built from a small skeleton of
   `LightProfinite`), whose Čech levels are coproducts of light profinite sets over the Hausdorff
   space `Y`.  `ℤ[covMap Y]` is then a resolution of `ℤ[Y]` (`Work.ANALYTIC.cech_descent_light`),
   and the levelwise comparison with the `Y × [0,1]`-side is a solid-equivalence
   (`Work.ANALYTIC.cechLevel_cov_solidEquiv`, from AN5 `Work.ANALYTIC.profinite_HI` and
   `ToolkitProp.sigma`); the levelwise Čech engine
   (`Work.ANALYTIC.solidEquiv_of_levelwise_cech`) and the identification of the condensed
   projection with `prTop Y` (`Work.ANALYTIC.solidEquiv_prTopI_dFree`) conclude.  The assembly is
   `Work.ANALYTIC.proj_solidEquiv'`.

`FlatProp` and `ToolkitProp` are proved in areas FLAT and TOOLKIT; AN1–AN3 in this area
(`Work.ANALYTIC.solidEquiv_cBounded'`, `Work.ANALYTIC.solidEquiv_boundedSeqIncl'`,
`Work.ANALYTIC.muT_solidEquiv`); AN5 is `Work.ANALYTIC.profinite_HI`.  So this statement has no
hypotheses.

(A second route, via the single stability input `SolidNull (ℤ[A]) → SolidNull (ℤ[ℤ[T] ⊗ A])` and
the general `kernel_prTop_tensor_top`, is developed as `Work.ANALYTIC.proj_solidEquiv_of` in
`Submission/Work/ANALYTIC/proj_solidEquiv.lean`.) -/
theorem hi_prop : Submission.Blueprint.HIProp :=
  _root_.Work.ANALYTIC.hi_prop_of_proj fun Y _ => proj_solidEquiv_leaf Y

end Work.ANALYTIC

/-- Convenience alias: the declaration above under the short name `Work.ANALYTIC.hi_prop`, for
callers that refer to this module's declaration by the requested name. -/
theorem hi_prop : Submission.Blueprint.HIProp :=
  _root_.Work.ANALYTIC.Work.ANALYTIC.hi_prop
