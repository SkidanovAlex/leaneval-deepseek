import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS_EllLimOK.PkgJets.clusterExtract
import Submission.Work.FTS_EllLimOK.PkgJets.hkMemOfJConv
import Submission.Work.FTS_EllLimOK.PkgJets.thetaBound
import Submission.Work.FTS_EllLimOK.PkgRepair
import Submission.Work.FTS_EllLimOK.UniqFatou
import Submission.Work.FTS_StreamBdry.Inputs.ftau_Dz_cont
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Stability.mul_rpow_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `PkgJets/boxDataD_uniform` — `BoxDataD` over the repaired packages

The proof decomposes into the five ingredient statements
`clusterExtract`, `pinningBound`, `thetaBound`, `hkMemOfJConv`, `slotSliceData`
(each delegated separately) and the assembly `boxDataD_of_clusterData` below.
-/

namespace Work.FTS_EllLimOK.PkgJets

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Subsequences of a `LimSeq4` -/


/-! ## `ℋ⁰` is inherited from the `/cos θ`-slot -/



/-! ## The assembly -/


/- **Alias repairing the constant name used in the requested statement.**  The area's vocabulary
lives in the underscore namespace `Work.FTS_EllLimOK` (`PkgRepair.lean`); the requested statement
below spells the target `Work.FTS.EllLimOK.BoxDataD`, which is not a name in this development
(`FTS_EllLimOK/NOTES.md` §10.4 records exactly this trap).  This definitions-only alias makes the
requested text elaborate to the intended `Prop`. -/
namespace Work.FTS.EllLimOK


end Work.FTS.EllLimOK


end Work.FTS_EllLimOK.PkgJets
