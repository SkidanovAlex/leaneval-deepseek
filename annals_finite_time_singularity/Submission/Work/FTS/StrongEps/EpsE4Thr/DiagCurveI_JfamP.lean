import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.EnergyFinalAssembly
import Submission.Work.FTS.StrongEps.EpsE4Thr.SlotDerivAll
import Submission.Work.FTS.StrongEps.EpsE4Thr.SlotHkGen.slot_L2_uniform_le_mixed
import Submission.Work.FTS.StrongEps.EpsE4Thr.integrable_cross_slot_rpow
import Submission.Work.FTS.StrongEps.EpsSlotLipP
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.LinPartArith
import Submission.Work.FTS.StrongEps.EpsZero.Nstar_zero_classC
import Submission.Work.FTS.StrongEps.PZeroAux.bumpHkNormBound
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option maxHeartbeats 2000000


end Work.FTS.StrongEps.EpsE4Thr
