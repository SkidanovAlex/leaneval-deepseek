import Submission.Work.RPB.Defs
import Submission.Work.RPB.B5.exists_lagFamily
import Submission.Work.RPB.B1a.exists_curveIsotopy
import Submission.Work.RPV.Glue

/-!
# `Work.RPB.Nodes`: the B-block nodes as `Work.RPV` node hypotheses

The assembly (`Submission/Work/RPV/Glue.lean`, `Submission/Work/RPV/Assemble.lean`) consumes the node
hypotheses `Work.RPV.CoreNode` (CORE), `Work.RPV.CurveIsotopyNode` (B1), `Work.RPV.LagFamilyNode`
(B5) and `Work.RPV.LagIsotopyNode` (A3).  This file supplies the two that live in this area:

* `lagFamilyNode : Work.RPV.LagFamilyNode`, an immediate application of
  `Work.RPB.B5.exists_lagFamily` (`Submission/Work/RPB/B5/exists_lagFamily.lean`, proved here; its
  import closure contains no `sorry`);
* `curveIsotopyNode : Work.RPV.CurveIsotopyNode`, an immediate application of
  `Work.RPB.B1a.exists_curveIsotopy` (`Submission/Work/RPB/B1a/exists_curveIsotopy.lean`), the
  conformal-map construction of the curve isotopy.  That construction is the geometric chain
  `Work.RPB.B1chain.loopFamily_chain_of_nodes` (smooth-boundary variant of
  `Work.RPB1a.loopFamily_chain_of_nodes`) applied to the node instances: N4
  `Work.RPB1a.jordan_domain_of_loop`, N4b `Work.RPB1a.collar_side`, N6 in the smooth-boundary form
  `Work.RPB.B1a.riemannMapNodeSmooth` (assembled from `Work.RPB.B1a.riemannMap_exists` — the ported
  Riemann-mapping result `Submission.Work.RPB.Port.RMT.Main` — and
  `Work.RPB.B1a.caratheodory_boundary_of_smooth`), N7 `Work.RPB1a.analytic_extension_of_collar`, and
  N8 `Work.RPB1a.discLoopFamily`; then `Work.RPB1a.curveIsotopy_of_loopFamily` and
  `Work.RPB1a.exists_homothetic_image_of_division` for the normalisation.

Everything outside this area — CORE (`Work.RPCore`) and A3 (`Work.RPA3`) — is supplied by the
sibling subprojects.

Note that the *other* direction of the B-block interface, `Work.RPB.B1p.area_pos_of_isotopy`
(node B1′: the signed area stays positive along an isotopy of embedded curves), is proved and is
used by neither side of this file; it remains available in `Submission/Work/RPB/B1p/`.
-/

open RectangularPegProblem

set_option autoImplicit false

namespace Work.RPB

/-- **B5 as a node**: `Work.RPB.B5.exists_lagFamily` *is* `Work.RPV.LagFamilyNode`. -/
theorem lagFamilyNode : Work.RPV.LagFamilyNode :=
  fun CI => B5.exists_lagFamily CI

/-- **B1 as a node**: `Work.RPB.B1a.exists_curveIsotopy` *is* `Work.RPV.CurveIsotopyNode`. -/
theorem curveIsotopyNode : Work.RPV.CurveIsotopyNode :=
  fun γ hγ => B1a.exists_curveIsotopy γ hγ

end Work.RPB
