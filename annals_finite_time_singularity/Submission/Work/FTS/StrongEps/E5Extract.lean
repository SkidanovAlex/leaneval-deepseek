import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsRLX.DeltaSlotEpsSq
import Submission.Work.FTS.StrongPersist.H6Row6.Basic
import Submission.Work.FTS.TransportS.t2SlotGuarded

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## `hequi` from the inputs of `EpsProfileLip_of_epsWP_corr` -/


/-! ## The extraction at every fake time -/


/-! ## The sequence producer with `ε ≤ 1` -/


end Work.FTS.StrongEps
