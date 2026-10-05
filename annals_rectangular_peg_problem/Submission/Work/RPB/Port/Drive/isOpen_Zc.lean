import Mathlib
import ChallengeDeps
import Submission.Work.RPB.Port.Measurable
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Submission.Work.RPB.Port.Drive.UmlaufSetup
import Submission.Work.RPB.Port.Geometry
import Submission.Work.RPB.Port.Collision
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.RPB.Port.Drive.curve_deriv_ne_zero

namespace Work.RPB.Port.Drive

open Manifold Topology Filter
open scoped Manifold ContDiff
open Work.RPB.Port.Collision (dirC)
open Work.RPB.Port.Configuration
open Work.RPB.Port.Geometry (eucNorm eucNorm_pos eucNorm_eq_zero)

/-! # `GoodC γ` is closed, i.e. `Zc γ` is open

`GoodC γ = {u | ∃ two chords of `γ` with equal midpoint, equal length and doubled directions
differing by `u`}`, and we show that it is closed *for any continuous injective `γ`*.

The point is that the `Sset`-decomposition of `GoodC γ`
(`Work.RPB.Port.Configuration.goodC_eq_iUnion`: `GoodC γ = ⋃ n, fst '' Sset γ n`) is an *increasing*
union of compact sets, so it gives no immediate information; but if `u k → u` with `u k ∈ GoodC γ`,
one passes to a convergent subsequence of the witnessing configurations.  In the limit, either the
first chord is nondegenerate — and then the midpoint/length/direction equations pass to the limit by
continuity (of `midPair`, `lenPair`, and of `dirPair` away from the diagonal), so that the limit
configuration is a witness for `u`; or the first chord is degenerate, in which case equal lengths force
the second chord to be degenerate too, all four points coincide at `γ z`, and both chords have
directions tending to the doubled direction of the tangent at `z`
(`chord_dirC_limit`), so that `u = 0`, which is always a collision angle
(`zero_mem_GoodC`: compare a chord with the reversed chord). -/

/-- The plane curve `t ↦ γ (Circle.exp t)` of a smooth embedded closed plane curve is `C¹`. -/
lemma contDiff_curve (γ : Circle → ℝ × ℝ)
    (hγ : IsSmoothEmbedding (𝓡 1) (𝓘(ℝ, ℝ × ℝ)) ∞ γ) : ContDiff ℝ 1 (curve γ) := by
  have hn1 : (1 : ℕ∞ω) ≤ ∞ := by simp
  have h1 : ContMDiff (𝓡 1) (𝓘(ℝ, ℝ × ℝ)) 1 γ := hγ.contMDiff.of_le hn1
  have h2 : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × ℝ)) 1 (curve γ) :=
    h1.comp (contMDiff_circleExp (m := 1))
  exact contMDiff_iff_contDiff.mp h2

end Work.RPB.Port.Drive
