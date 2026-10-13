import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.H2.DivQ.sqIntervalIntegralLe

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Copyright: work module for the Elgindi finite-time singularity project (area `FTS.EllSol`).

# The `L²` Cauchy–Schwarz inequality for interval integrals

For `a ≤ b` and a continuous `f : ℝ → ℝ`,

  `(∫_{a}^{b} |f|)² ≤ (b - a) · ∫_{a}^{b} f²`.

This is the `L²` Cauchy–Schwarz inequality applied to the pair of functions `(|f|, 1)` on the
interval `(a, b]`, whose second `L²` norm is `b - a`.  The analytic content is delegated to
`Work.FTS.H2.DivQ.sqIntervalIntegralLe` (Cauchy–Schwarz for the interval integral of a general
interval-integrable function, itself derived from the abstract Cauchy–Schwarz inequality on
`L²`); here we only specialise it to `|f|` and use `|f|² = f²`.

The lemma is the sibling of `gcTail` in this directory, which consumes it to bound
`(Gc N b u t θ)²` by `4N ∫ (∂ₜu - b u)²` off the truncation window.
-/

namespace Work.FTS.EllSol.ShiftFT.Aux2

/-- **Cauchy–Schwarz for the interval integral.**  For `a ≤ b` and continuous `f`,
`(∫_{a}^{b} |f|)² ≤ (b - a) ∫_{a}^{b} f²`. -/
theorem sqIntegralAbsLe (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ x in a..b, |f x|) ^ 2 ≤ (b - a) * ∫ x in a..b, (f x) ^ 2 := by
  have habs : Continuous fun x : ℝ => |f x| := hf.abs
  have h := Work.FTS.H2.DivQ.sqIntervalIntegralLe (fun x : ℝ => |f x|) hab
    (habs.intervalIntegrable a b) ((habs.pow 2).intervalIntegrable a b)
  have h2 : (∫ x in a..b, (|f x|) ^ 2) = ∫ x in a..b, (f x) ^ 2 :=
    intervalIntegral.integral_congr (fun x _ => sq_abs (f x))
  rwa [h2] at h

end Work.FTS.EllSol.ShiftFT.Aux2
