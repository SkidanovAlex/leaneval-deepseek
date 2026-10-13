import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts
import Submission.Work.FTS.EllipticEst.FstarDivOpen.fstar_div_integrable_of_smoothOpen
import Submission.Work.FTS.NonlinRows.NRow1_7Aux
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior
import Submission.Work.FTS.H2.L12HQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.ClassCRHS

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The radial function `z ↦ L₁₂(w)(z)` is `C^∞` on `(0,∞)`, hence `SmoothOpen` on the open
quadrant, for every profile `w` of the class `ClassC α`.**

`L₁₂(w)` is the tail integral `z ↦ ∫_z^∞ F_*(w)(r)/r dr` (`Work.Elliptic.L12_eq_radial`), so its
derivative on `(0,∞)` is `z ↦ -3 F_*(w)(z)/z` (`HasDerivAt_L12_of_Fstar_facts`).  For a profile of
the class `ClassC α` all three ingredients are available:

* `F_*(w)` is `C^∞` on `(0,∞)` — the field `ClassC.fsm`;
* `r ↦ F_*(w)(r)/r` is integrable on `(0,∞)` (`FstarDivOpen.fstar_div_integrable_of_smoothOpen`,
  from the fields `ClassC.reg` (`SmoothOpen w`) and `ClassC.mem` (`HkMem α 7 w`));
* consequently `z ↦ -3 F_*(w)(z)/z` is `C^∞` on `(0,∞)`, and the primitive lemma
  `contDiffOn_infty_iff_deriv_of_isOpen` upgrades `L₁₂(w)` to `C^∞` there.

Promoting the radial smoothness to the open quadrant is `NonlinRows.smoothOpen_radial`, and the
two definitions of `L₁₂` are identified by `Work.FTS.H2.constructionL12_eq_ellipticL12`. -/
theorem smoothOpen_L12_radial_classC {α : ℝ} {w : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hw : Work.FTS.ClassC.ClassC α w) :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 w z) := by
  have hFint : IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar w r / r) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.FstarDivOpen.fstar_div_integrable_of_smoothOpen α 7 w hw.reg hw.mem
  have hderiv := Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts w hw.fsm hFint
  have hgTop : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => -(3 * Work.Elliptic.Fstar w z / z)) (Set.Ioi 0) :=
    ((contDiffOn_const.mul (contDiffOn_infty.mpr hw.fsm)).div contDiffOn_id
      (fun z hz => ne_of_gt hz)).neg
  have hTop : ContDiffOn ℝ Work.Stability.smoothOrder (Work.Elliptic.L12 w) (Set.Ioi 0) := by
    rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi]
    exact ⟨fun z hz => (hderiv z hz).differentiableAt.differentiableWithinAt,
      hgTop.congr (fun z hz => (hderiv z hz).deriv)⟩
  refine Work.FTS.NonlinRows.smoothOpen_radial
    (r := fun z => Work.Construction.L12 w z) fun n => ?_
  refine (contDiffOn_infty.mp hTop n).congr fun z hz => ?_
  rw [Work.FTS.H2.constructionL12_eq_ellipticL12 w]

end Work.FTS.StrongEps.ClassCRHS
