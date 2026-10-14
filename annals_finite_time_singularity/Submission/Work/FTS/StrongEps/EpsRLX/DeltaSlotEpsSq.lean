import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Submission.Work.FTS.StrongEps.EpsProfileLip_of_epsWP
import Submission.Work.FTS.StrongEps.EpsRHSP_slotSup_corr_fam
import Submission.Work.FTS.StrongEps.EpsRLX.DeltaSlotJeps
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.LinPartAux
import Submission.Work.FTS.StrongEps.EpsSqTools.Shift
import Submission.Work.FTS.StrongEps.PZeroAux.mixed_Pz
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.epsWP_abs_le_on_compact
import Submission.Work.FTS.StrongEps.wtZ_shift_le
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkDzdIterSharp
import Submission.Work.FTS.StrongPersist.H6Row6.Basic
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNstarBlock
import Submission.Work.FTS.StrongPersist.StarPkg6Assembly
import Submission.Work.FTS.StrongPersist.SupOpenH2
import Submission.Work.FTS.TransportS.t2SlotGuarded
import Submission.Work.Spaces.pz_DthIter_mul_eq
-- ===== merged: Submission.Work.FTS.StrongEps.EpsProfileLip_of_epsWP_corr =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps


end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.DeltaSlotEpsSq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## The `ε`-weight vanishes off the open quadrant

The weight `epsW α z θ = w z / sin(2θ)^{γ/2}` degenerates on the three coordinate lines that make
up the boundary of the closed quadrant `Iz ×ˢ Iθ`: at `z = 0` because `w 0 = 0`, and at
`θ = 0, π/2` because `sin(2θ) = 0` and `γ/2 ≠ 0` (Lean's totalised inversion then gives `0`).
Consequently `EpsSq`/`EpsMem` only see the values of a datum on the *open* quadrant `Q0`, which is
what the projection identity `mixed b a (Pz f) = mixed b a f - c · mixed b a bump` (proved on `Q0`
by `PZeroAux.mixed_Pz`) can be transferred along. -/





/-! ## Almost-everywhere strong measurability of the slots -/




end Work.FTS.StrongEps.EpsRLX
end
