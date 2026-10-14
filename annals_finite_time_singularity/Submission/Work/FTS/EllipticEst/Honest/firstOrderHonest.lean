import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.HkNorm_Dz_le_open
import Submission.Work.FTS.EllipticEst.Honest.FOH.psiRho
import Submission.Work.FTS.EllipticEst.Honest.HonSliceFinite
import Submission.Work.FTS.EllipticEst.Honest.Step1.pthCore
import Submission.Work.FTS.EllipticEst.Honest.honSliceIntFacts
import Submission.Work.FTS.EllipticEst.Honest.honYcBound
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

open MeasureTheory
open scoped ENNReal

/-! ## The `HkMem ↔ σ` transfer lemmas

`HkIntegrand α 0 g z θ = (g z θ · w z / sin(2θ)^{η/2})²`, and on `Iθ` the pointwise identity
`(g z θ · (w z / sin(2θ)^{η/2}))² = (w z)² · (g z θ)² · sin(2θ)^{-η}` holds
(`sq_profile_eq`).  This is the bridge between the `HkMem`/`HkSq` vocabulary and the slice
lemmas of the `Honest` chapter, which are stated with the weight `σ θ = sin(2θ)^{-η}`
(`AngSecond.sig = sEta`). -/

/-- **Pointwise normalisation of the level-`0` integrand.**  On `Iθ`,
`HkIntegrand α 0 g z θ = (w z)² · ((g z θ)² · σ θ)`. -/
theorem hkIntegrand_eq_w_sq (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (Work.Spaces.w z) ^ 2 * ((g z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) := by
  rw [HkIntegrand_zero_eq α g z θ,
    sq_profile_eq g z θ (sin_two_nonneg_of_mem_Iθ hθ)]
  simp only [Work.FTS.EllipticEst.AngSecond.sig]
  ring







end Work.FTS.EllipticEst.Honest
