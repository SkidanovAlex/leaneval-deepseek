import Mathlib
import Submission.Work.RPA3.Bridge
import Submission.Work.RPV.Glue

/-!
# RPA3: block A3 as the route's node `LagIsotopyNode`

The glue of subproject `RPV` (`Submission/Work/RPV/Glue.lean`) expects the four geometric nodes of
the route as hypotheses, among them

`Work.RPV.LagIsotopyNode` : a `LagFamily` is induced by a compactly supported Hamiltonian flow.

`Work.RPA3.rpv_lag_isotopy_extension` *is* that statement (the two have the same type), so block A3
plugs into the glue directly — no restatement, no conversion.  This module records that fact as a
type-checked theorem, and composes it with the other three nodes in
`Work.RPA3.main_rect_of_nodes_with_A3`.

This is the only module of this directory that imports the `RPV` aggregation.
-/

open RectangularPegProblem Manifold Complex Real
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPA3

/-- **A3, as the route's node.**  `Work.RPA3.rpv_lag_isotopy_extension` is the `RPV` glue's
`LagIsotopyNode`. -/
theorem rpv_LagIsotopyNode : Work.RPV.LagIsotopyNode :=
  rpv_lag_isotopy_extension

/-- The main rectangle-existence theorem from the three remaining geometric nodes, with block A3
supplied by this subproject. -/
theorem main_rect_of_nodes_with_A3 (hC : Work.RPV.CoreNode) (hB1 : Work.RPV.CurveIsotopyNode)
    (hB5 : Work.RPV.LagFamilyNode) (γ : Circle → ℂ)
    (hγ : Work.RPV.IsSmoothJordan γ) (φ : ℝ) (h0 : 0 < φ) (h1 : φ < π) :
    Work.RPV.HasThetaRect (Set.range γ) φ :=
  Work.RPV.main_rect_of_nodes hC hB1 hB5 rpv_LagIsotopyNode γ hγ φ h0 h1

end Work.RPA3
