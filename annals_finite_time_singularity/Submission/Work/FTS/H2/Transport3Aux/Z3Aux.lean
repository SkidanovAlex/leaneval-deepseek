import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Coercivity.wip_L_self
import Submission.Work.FTS.H2.IbpHardEta
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS_EllLimOK.BoxDataH.BoxUniform
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall
-- ===== merged: Submission.Work.FTS.H2.HardSlotBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Integrability transfer lemmas -/





end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.H2.IbpHardMixedBlock =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Weight algebra at the angular endpoints

For `s ≥ 0` and exponents `q` avoiding the critical values, the powers of `s` combine as in
the exponential notation (both sides vanish at `s = 0`, which is why only the non-vanishing
of the exponents has to be assumed). -/


/-- `s^{-q}·s² = s^{2-q}` for `s ≥ 0` and `q ≠ 2`. -/
private lemma rpow_neg_mul_sq (s q : ℝ) (hs : 0 ≤ s) (hq : q ≠ 2) :
    s ^ (-q) * s ^ 2 = s ^ (2 - q) := by
  have h2 : s ^ (2 : ℝ) = s ^ 2 := Real.rpow_natCast s 2
  have hne : (-q) + 2 ≠ 0 := by intro h; exact hq (by linarith)
  rw [← h2, ← Real.rpow_add' (x := s) (y := -q) (z := (2 : ℝ)) hs hne]
  rw [show (-q) + 2 = 2 - q by ring]

/-! ## The pointwise algebra of the factorization `w = sin(2θ)·u`

The three identities below rewrite the two integrands of the integration by parts for a block
`w = D_z^j D_θ^{i'+1} g` which carries the factor `sin(2θ)` (so that `w = sin(2θ)·u` with
`u = D_z^j ∂_θ D_θ^{i'} g`), the singular weight `sin(2θ)^{-q}` being absorbed by two powers
of `sin(2θ)` coming from the two factors `w`. -/





end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.H2.Transport3Aux.Z3Aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.Transport3Aux
namespace Z3

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Peeling a single index out of a double `range`-sum -/





/-! ## The slot cancellation of the mismatch family -/



/-! ## The order bound of the surviving mixed blocks -/


/-! ## The pointwise bounds of the Leibniz summands -/



/-! ## The expansion of the `D_z`-pairing, and the cancellation of `Mismatchz` -/



/-! ## The aggregate bounds for `easyZ` and `Msurv` -/
end Z3
end Work.FTS.H2.Transport3Aux
end
end
