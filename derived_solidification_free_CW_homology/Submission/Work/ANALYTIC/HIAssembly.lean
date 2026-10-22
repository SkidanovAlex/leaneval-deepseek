import Mathlib
import Submission.Work.ANALYTIC.HICond
import Submission.Work.ANALYTIC.solidEquiv_of_levelwise_cech
import Submission.Work.ANALYTIC.cechLevel_cov_solidEquiv
import Submission.Work.ANALYTIC.solidEquiv_prTopI_dFree
import Submission.Work.ANALYTIC.profinite_HI
import Submission.Work.ANALYTIC.hi_prop_of_proj

/-!
# AN6, assembly: the projection form for Hausdorff spaces, via the Čech route

This module assembles the Čech route to `Work.ANALYTIC.proj_solidEquiv` (REFS/04 §3):

* `Work.ANALYTIC.covMap (Y) : cov Y ⟶ Y` is a sectionwise split epimorphism (AN6 step 2,
  `Submission/Work/ANALYTIC/HISetup.lean`);
* the levelwise comparison of the two Čech resolutions (`Y × [0,1]` vs `Y`) is a solid-equivalence
  (`Work.ANALYTIC.cechLevel_cov_solidEquiv`);
* the levelwise Čech engine (`Work.ANALYTIC.solidEquiv_of_levelwise_cech`) then produces a
  solid-equivalence for the condensed projection `prTopI Y`, which is transported to `dFree
  (prTop Y)` (`Work.ANALYTIC.solidEquiv_prTopI_dFree`).
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

namespace Work.ANALYTIC

attribute [local instance] lightCondSetHasCoproduct

/-- **The projection form of homotopy invariance, Čech route.**  For every Hausdorff space `Y` the
projection `pr : Y × [0,1] ⟶ Y` induces a solid-equivalence `ℤ[Y × [0,1]] ⟶ ℤ[Y]`. -/
theorem proj_solidEquiv' (Y : TopCat.{0}) [T2Space Y] :
    Submission.Blueprint.SolidEquiv (Submission.Blueprint.dFree (Work.ANALYTIC.prTop Y)) :=
  solidEquiv_prTopI_dFree Y
    (solidEquiv_of_levelwise_cech (covMap Y) (covMap_epi Y) (covMapI Y) (epi_covMapI Y)
      (covProj Y) (prTopI Y) (cov_square Y) (cechLevel_cov_solidEquiv Y))

end Work.ANALYTIC
