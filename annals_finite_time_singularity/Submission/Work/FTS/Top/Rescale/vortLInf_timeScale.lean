import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.Top.Rescale.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Top.Rescale

/-
The `L^∞` norm of the vorticity, `Work.LWP.vortLInf u t = ⨆ x, ‖vorticity (u · t) x‖`, scales by
`c` under the time rescaling; the space variable is *not* rescaled, so there is no `c²` factor:

  `vortLInf (timeScale c u) t = c * vortLInf u (c * t)`   for `c ≥ 0`.

Route: `Work.FTS.Top.vorticity_timeScale` gives
`vorticity (timeScale c u · t) = fun x => c • vorticity (u · (c*t)) x`, and `‖c • w‖ = c * ‖w‖`
for `c ≥ 0`, so with `f x = ‖vorticity (u · (c*t)) x‖ ≥ 0` the claim is the real identity

  `(⨆ x, c * f x) = c * (⨆ x, f x)`   for `c ≥ 0`.

That identity is unconditional: for `c = 0` both sides are `0`; for `c > 0` the range of `c * f ·`
is bounded above exactly when the range of `f` is, so the junk value `sSup ∅ = 0` is on both sides
simultaneously.  It is Mathlib's `Real.mul_iSup_of_nonneg` (`Real.sSup_smul_of_nonneg` for a
positive scaling, `Real.sSup_of_not_bddAbove` otherwise), so no case split is needed here.
Namespace `Work.FTS.Top`.
-/
/-- The pointwise norm of the rescaled vorticity slice, `c ≥ 0`: `‖c • w‖ = c * ‖w‖`. -/
theorem norm_smul_of_nonneg {c : ℝ} (hc : 0 ≤ c) (w : Work.FTS.Top.R3) :
    ‖c • w‖ = c * ‖w‖ := by
  rw [norm_smul, Real.norm_of_nonneg hc]

theorem vortLInf_timeScale (c : ℝ) (hc : 0 ≤ c) (u : Work.FTS.Top.R3 → ℝ → Work.FTS.Top.R3)
    (t : ℝ) :
    Work.LWP.vortLInf (Work.FTS.Top.timeScale c u) t = c * Work.LWP.vortLInf u (c * t) := by
  -- `vortLInf` is the `iSup` of the pointwise norms of the vorticity slice.
  unfold Work.LWP.vortLInf
  -- The rescaled slice's vorticity is `c •` the original slice's vorticity, and `‖c • w‖ = c ‖w‖`
  -- when `c ≥ 0`; so the two `iSup`s are taken of `x ↦ c * f x` and `f`, with `f ≥ 0`.
  have hv : (fun x => ‖FiniteTimeSingularity.vorticity (Work.FTS.Top.timeScale c u · t) x‖)
      = fun x => c * ‖FiniteTimeSingularity.vorticity (u · (c * t)) x‖ := by
    rw [Work.FTS.Top.vorticity_timeScale]
    funext x
    exact norm_smul_of_nonneg hc _
  rw [hv]
  -- Pull the factor `c` out of the `iSup`.  `Real.mul_iSup_of_nonneg` is unconditional in `ℝ`:
  -- both sides are the junk value `0` when the range is unbounded above, and `0` for `c = 0`.
  exact (Real.mul_iSup_of_nonneg hc
    (fun x => ‖FiniteTimeSingularity.vorticity (u · (c * t)) x‖)).symm

end Work.FTS.Top.Rescale
