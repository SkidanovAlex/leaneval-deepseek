/-
Copyright: work module for the Elgindi finite-time singularity project.

# `ProfRHSAux/Basic` — aggregator for the `profRHS` trace toolkit

Imports the pieces: `Extract` (pointwise bounds from the honest norms), `OpAdd` (linearity of
`ℛ, U, V`), `L12Add` (additivity of `L₁₂` over `F_* + W`), `StreamDefs`, `StreamOps` (the split of
the total stream function and the operator identities) and `Bounds` (the pointwise bounds).
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.Extract
import Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.OpAdd
import Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.L12Add
import Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.StreamDefs
import Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.StreamOps
import Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.Bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX.ProfRHSAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

