/-
Copyright: work module for the Elgindi finite-time singularity project.

Right-continuity at `0` of the integration-by-parts boundary term `htPP f` of
`hardy_two`, using only the two sup-norm bounds of `u = htU f = f / sin 2θ` and of
its derivative on the *open* interval `(0, π/2)`, as supplied by the near-endpoint
estimates `htU_near_zero` / `htU_near_pi2`.

Since `htPP f θ = sin(2θ) * (40 cos(2θ) u'(θ)² - 80 sin(2θ) u(θ) u'(θ))` and the
factor in parentheses is bounded by `40 Cu'² + 80 Cu Cu'` as soon as `|u| ≤ Cu`,
`|u'| ≤ Cu'` with `Cu, Cu' ≥ 0`, while `sin 2θ → 0`, a squeeze yields
`htPP f θ → 0 = htPP f 0` as `θ → 0` along `[0, π/2]`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Elliptic.HardyTwoDefs
import Submission.Work.Elliptic.abs_htPP_le_sin
import Submission.Work.Elliptic.tendsto_abs_sin_two_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

theorem continuousWithinAt_htPP_zero (f : ℝ → ℝ) (Cu Cu' : ℝ)
    (hu : ∀ x ∈ Set.Ioo 0 (π / 2), |Work.Elliptic.htU f x| ≤ Cu)
    (hu' : ∀ x ∈ Set.Ioo 0 (π / 2), |deriv (Work.Elliptic.htU f) x| ≤ Cu') :
    ContinuousWithinAt (Work.Elliptic.htPP f) (Set.Icc 0 (π / 2)) 0 := by
  -- The hypothesis bounds are non-vacuous only for nonnegative `Cu`, `Cu'`.
  have hpi4 : π / 4 ∈ Set.Ioo 0 (π / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have hCu : 0 ≤ Cu := le_trans (abs_nonneg _) (hu (π / 4) hpi4)
  have hCu' : 0 ≤ Cu' := le_trans (abs_nonneg _) (hu' (π / 4) hpi4)
  -- Pointwise majorant on the whole closed interval.
  have hbound : ∀ θ ∈ Set.Icc 0 (π / 2),
      |htPP f θ| ≤ |Real.sin (2 * θ)| * (40 * Cu' ^ 2 + 80 * Cu * Cu') :=
    abs_htPP_le_sin f hCu hCu' hu hu'
  -- Squeeze: `|htPP f θ| → 0`, hence `htPP f θ → 0 = htPP f 0`.
  have hsq : Tendsto (fun θ : ℝ => |htPP f θ|) (𝓝[Set.Icc 0 (π / 2)] 0) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun θ => abs_nonneg _))
      (eventually_nhdsWithin_of_forall hbound) (tendsto_abs_sin_two_mul _)
  have h : Tendsto (htPP f) (𝓝[Set.Icc 0 (π / 2)] 0) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa [Real.norm_eq_abs] using hsq)
  rwa [ContinuousWithinAt, htPP_zero f]

end Work.Elliptic
