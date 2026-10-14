import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.LocData.DzIter_FM_Fstar_abs_le
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FzFacts
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.Regularity.hkIntegrandZfarBound
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.c2mGam_Wt_bound
import Submission.Work.FTS.StrongPersist.N6Trans.IP4T1Aux
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.ThetaJets.ClassC_le
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2W.asliceMomentEq
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 3200000

noncomputable section

/-! ## Unconditional linearity of the `D`-operators over constant multiples

`mixed j i (fun z θ => c * f z θ) = c * mixed j i f z θ` holds for **every** constant `c` and
every `f`, with no regularity hypothesis: if `f` is not differentiable at a point then neither
is `c * f` (for `c ≠ 0`) and both sides are `0`.  This is the same observation as
`Work.FTS.LocData.deriv_const_mul_uncond`; it is needed here to pull the factor `-2` of
`N₂^{ss} = -2 U(Φ̃_*) ∂_θF_*` out of the Leibniz expansion. -/

private theorem deriv_cmul (c x : ℝ) (f : ℝ → ℝ) :
    deriv (fun y => c * f y) x = c * deriv f x := by
  rcases eq_or_ne c 0 with h | h
  · subst h; simp
  · rcases em (DifferentiableAt ℝ f x) with hf | hf
    · exact deriv_const_mul c hf
    · have h2 : ¬ DifferentiableAt ℝ (fun y => c * f y) x := by
        intro hh
        apply hf
        have he : f = fun y => c⁻¹ * (c * f y) := by
          funext y; rw [← mul_assoc, inv_mul_cancel₀ h, one_mul]
        rw [he]
        exact hh.const_mul c⁻¹
      rw [deriv_zero_of_not_differentiableAt hf,
        deriv_zero_of_not_differentiableAt h2, mul_zero]

private theorem pz_cmul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pz (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.pz f z θ := by
  funext z θ
  simp only [Work.Spaces.pz]
  rw [deriv_cmul]

private theorem Dz_cmul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.Dz f z θ := by
  funext z θ
  simp only [Work.Spaces.Dz]
  rw [pz_cmul]
  ring

private theorem pth_cmul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.pth f z θ := by
  funext z θ
  simp only [Work.Spaces.pth]
  rw [deriv_cmul]

private theorem Dth_cmul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dth (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.Dth f z θ := by
  funext z θ
  simp only [Work.Spaces.Dth]
  rw [pth_cmul]
  ring




/-! ## Smoothness of `U(Φ̃_*)` on the open quadrant -/


/-! ## The row-15 pointwise estimate on a "good" angular slice

Everything is proved here from the delivered U-side bounds (`Uop_PhiTs_bounds`), leaving the two
`F_*`-side inputs (`row15_SmoothQuadPthFstar`, `row15_PthFstarMixed`) as explicit hypotheses so
that the argument can be checked independently of them. -/




end

end Work.FTS.Nonlinear.Pieces.RNP
