import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Blocks.InterpTrunc.zF_abs_le
import Submission.Work.FTS.EllipticEst.Alpha4.integrable_slice_pthDz_sigma
import Submission.Work.FTS.EllipticEst.RPFresh.slice_z_integrable
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceDefs
import Submission.Work.FTS.TransportS.SupDzWeighted.supDz_weighted_avg_le
import Submission.Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.SolutionDelivery.Scaling.vorticityDecay_rescaleDatum
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.Blocks.InterpTrunc.assembly =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks.InterpTrunc

set_option autoImplicit false






end Work.Blocks.InterpTrunc
end
end
-- ===== merged: Submission.Work.Blocks.InterpTrunc.cut_functional_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks.InterpTrunc

set_option autoImplicit false

/-! ## Elementary facts about `w` and `sl` -/

theorem w_zero : Work.Spaces.w 0 = 0 := by
  simp [Work.Spaces.w]




/-! ## The three slicewise estimates for the truncation -/




/-! ## The arithmetic of the coefficients -/


/-! ## The main estimate -/


end Work.Blocks.InterpTrunc
end
end
