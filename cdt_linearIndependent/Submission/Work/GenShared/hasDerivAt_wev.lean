import Mathlib
import Submission.Work.GenShared.wevD

/-!
# `Wev y1 J n` is differentiable with derivative `WevD y1 J n z`

`Wev y1 J n z = Rval n.1 z * y1 z + Rval n.2.1 z * deriv y1 z + ∑ i, Rval (n.2.2 i) z * J i z`
is the evaluation of a coefficient tuple `n : W k` at `z` (`Work.GenShared.periods_defs`) and
`WevD y1 J n z` is its formal derivative (`Work.GenShared.wevD`),
`Rval (dRat n.1) z*y1 z + Rval n.1 z*y1' z + Rval (dRat n.2.1) z*y1' z + Rval n.2.1 z*y1'' z
 + Σᵢ (Rval (dRat (n.2.2 i)) z*Jᵢ z + Rval (n.2.2 i) z*Jᵢ' z)`.

This file proves that at every point `z` of the ball at which all coefficients of `n` are regular,
`Wev y1 J n` really does have derivative `WevD y1 J n z`, provided `y1` and the `J i` are complex
differentiable on the ball.

The only non-elementary point is the term `Rval n.2.1 z * deriv y1 z`: it requires the *second*
derivative of `y1`, i.e. `HasDerivAt (deriv y1) (deriv (deriv y1) z) z`.  This is where complex
analysis enters: `DifferentiableOn ℂ y1 (ball x₀ δ)` on the *open* ball makes `y1` analytic there
(`DifferentiableOn.analyticOnNhd`), and the derivative of an analytic function is again analytic
(`AnalyticOnNhd.deriv`), hence `deriv y1` is differentiable at the interior point `z`.  The
remaining terms are the product rule (`HasDerivAt.mul`) applied to `hasDerivAt_rval`
(`(Rval f)' = Rval (dRat f)`) and to the differentiability of `y1`, of `deriv y1` and of the
`J i`; the `∑`-term is `HasDerivAt.sum` preceded by the pointwise rewriting
`Finset.sum_apply` of the function `∑ i, fun w => …` into `fun w => ∑ i, …`.
-/

namespace Work.GenShared

open Complex Metric Work.GenShared
open Submission.CDT (dRat)

theorem hasDerivAt_wev {k : ℕ} (y1 : ℂ → ℂ) (J : Fin k → ℂ → ℂ) (x0 : ℂ) {δ : ℝ}
    (hy1d : DifferentiableOn ℂ y1 (Metric.ball x0 δ))
    (hJd : ∀ i, DifferentiableOn ℂ (J i) (Metric.ball x0 δ))
    {n : Work.GenShared.W k} {z : ℂ} (hz : z ∈ Metric.ball x0 δ)
    (ha : Work.GenShared.Rreg n.1 z) (hb : Work.GenShared.Rreg n.2.1 z)
    (hc : ∀ i, Work.GenShared.Rreg (n.2.2 i) z) :
    HasDerivAt (Work.GenShared.Wev y1 J n) (Work.GenShared.WevD y1 J n z) z := by
  -- `z` is an interior point of the ball
  have hzmem : Metric.ball x0 δ ∈ nhds z := Metric.isOpen_ball.mem_nhds hz
  -- on the open ball `y1` is analytic, and so is its derivative
  have hy1A : AnalyticOnNhd ℂ y1 (Metric.ball x0 δ) := hy1d.analyticOnNhd Metric.isOpen_ball
  have hdy1 : DifferentiableAt ℂ y1 z := hy1A.differentiableOn.differentiableAt hzmem
  have hdy1' : DifferentiableAt ℂ (deriv y1) z :=
    (hy1A.deriv.differentiableOn).differentiableAt hzmem
  -- the three blocks `Rval n.1 * y1`, `Rval n.2.1 * deriv y1`, `∑ i, Rval (n.2.2 i) * J i`
  have h1 : HasDerivAt (fun w => Rval n.1 w * y1 w)
      (Rval (dRat n.1) z * y1 z + Rval n.1 z * deriv y1 z) z :=
    (hasDerivAt_rval n.1 z ha).mul hdy1.hasDerivAt
  have h2 : HasDerivAt (fun w => Rval n.2.1 w * deriv y1 w)
      (Rval (dRat n.2.1) z * deriv y1 z + Rval n.2.1 z * deriv (deriv y1) z) z :=
    (hasDerivAt_rval n.2.1 z hb).mul hdy1'.hasDerivAt
  have h3 : HasDerivAt (fun w => ∑ i, Rval (n.2.2 i) w * J i w)
      (∑ i, (Rval (dRat (n.2.2 i)) z * J i z + Rval (n.2.2 i) z * deriv (J i) z)) z := by
    -- write the pointwise sum as a sum of functions, so that `HasDerivAt.sum` applies
    rw [show (fun w : ℂ => ∑ i, Rval (n.2.2 i) w * J i w)
        = (∑ i : Fin k, fun w : ℂ => Rval (n.2.2 i) w * J i w) from
      funext (fun w => by simp [Finset.sum_apply])]
    exact HasDerivAt.sum (u := Finset.univ)
      (A := fun i w => Rval (n.2.2 i) w * J i w)
      (A' := fun i => Rval (dRat (n.2.2 i)) z * J i z + Rval (n.2.2 i) z * deriv (J i) z)
      (fun i _ => (hasDerivAt_rval (n.2.2 i) z (hc i)).mul
        (((hJd i).differentiableAt hzmem).hasDerivAt))
  have hmain := (h1.add h2).add h3
  -- only the parenthesisation of the value has to be adjusted
  have hval : ((Rval (dRat n.1) z * y1 z + Rval n.1 z * deriv y1 z)
        + (Rval (dRat n.2.1) z * deriv y1 z + Rval n.2.1 z * deriv (deriv y1) z))
        + ∑ i, (Rval (dRat (n.2.2 i)) z * J i z + Rval (n.2.2 i) z * deriv (J i) z)
      = WevD y1 J n z := by
    simp only [WevD]
    ring
  rw [← hval]
  exact hmain

end Work.GenShared
