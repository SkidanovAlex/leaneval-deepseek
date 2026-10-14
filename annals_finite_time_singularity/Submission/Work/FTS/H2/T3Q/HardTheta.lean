import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.H2.T1Defs
import Submission.Work.FTS.H2.T1HardSlice
import Submission.Work.FTS.H2.T3Q.Msurv_abs_le_Q
import Submission.Work.FTS.H2.Transport3Aux.Z3Aux
import Submission.Work.FTS.H2.WPQ.Interior
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.integral_sin_two_rpow_neg
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS_EllLimOK.BoxDataH.BoxUniform
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.SlotOpen
import Submission.Work.H2.T1Q.T1EasyContQ
import Submission.Work.SolutionDelivery.Scaling.vorticityDecay_rescaleDatum
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall
-- ===== merged: Submission.Work.FTS.H2.T3Q.EasyTheta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.T3Q

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## Vanishing of the two weights (and of `T1Easy`) on the boundary lines

`T1Easy α f g = H4PairInt α (f·D_θg) g - T1Hard α f g` is a finite sum of terms each of which
carries a factor `Whz²` resp. `Wm²` (in `H4PairInt`) or a factor `w² sin(2θ)^{-q}` (in
`T1Hard`).  Both weights vanish on the two angular boundary lines `θ = 0`, `θ = π/2`
(`sin(2θ) = 0` and the exponents `η/2`, `γ/2` are positive) and on the radial line `z = 0`
(`w 0 = 0`).  Since `HkIntegrand α 4 g` also vanishes where `sin(2θ) = 0`, the pointwise bound
of `EasyTheta` is trivial on the boundary and the Leibniz expansion (which is available on the
open quadrant only) only has to be invoked in the interior. -/


theorem eta_ne_zero : Work.Spaces.eta ≠ 0 := by
  unfold Work.Spaces.eta; norm_num









end Work.FTS.H2.T3Q
end
-- ===== merged: Submission.Work.FTS.H2.T3Q.GoodZPt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.T3Q

open scoped Real Topology
open Work.FTS.H2.Transport3Aux.Z3

set_option autoImplicit false
set_option maxHeartbeats 1600000


end Work.FTS.H2.T3Q
end
-- ===== merged: Submission.Work.FTS.H2.T3Q.HardTheta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real
open MeasureTheory Set Filter

namespace Work.FTS.H2.T3Q


end Work.FTS.H2.T3Q
end
