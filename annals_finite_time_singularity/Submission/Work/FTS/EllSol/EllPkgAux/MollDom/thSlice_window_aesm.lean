import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.aeStronglyMeasurable_exp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open scoped Real Topology
open MeasureTheory Set Filter

/-- **A.e. strong measurability of the windowed angular second derivative of the trace datum.**

The datum `G` is `C^∞` on the open quadrant (first component of `TraceClass`), so the uncurried
`(z,θ) ↦ (∂_θ²G z θ)²` is continuous there; composing with the continuous map
`p ↦ (exp p.1, p.2)` and observing that the half strip `ℝ × (0,π/2)` has full measure for
`volume.prod (volume.restrict Iθ)` (`aeStronglyMeasurable_exp`) gives the (unwindowed) a.e.
strong measurability.  Multiplying by the indicator of the measurable window
`{p | |log z - p.1| ≤ δ}` (a closed slab in the logarithm of the radius) gives the statement.

No hypothesis on `δ` or on the sign of `z` is needed: the window is a closed (possibly empty)
interval, and its indicator is measurable regardless. -/
theorem thSlice_window_aesm (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (δ z : ℝ) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => if |Real.log z - p.1| ≤ δ then
        (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp p.1) p.2) ^ 2 else 0)
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  -- the unwindowed angular second derivative is continuous on the open quadrant
  have hcont : ContinuousOn (Function.uncurry
      (fun z θ => (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2))
      Work.FTS.EllipticEst.Q0 :=
    ((hT.1.pth).pth).continuousOn.pow 2
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp p.1) p.2) ^ 2)
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    aeStronglyMeasurable_exp
      (X := fun z θ => (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2) hcont
  -- the window is a measurable set
  have hmeas : Measurable (fun p : ℝ × ℝ => |Real.log z - p.1|) :=
    (continuous_const.sub continuous_fst).abs.measurable
  have hS : MeasurableSet {p : ℝ × ℝ | |Real.log z - p.1| ≤ δ} :=
    measurableSet_Iic.preimage hmeas
  -- the windowed function is the indicator of the window applied to the unwindowed one
  rw [show (fun p : ℝ × ℝ => if |Real.log z - p.1| ≤ δ then
        (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp p.1) p.2) ^ 2 else 0)
      = {p : ℝ × ℝ | |Real.log z - p.1| ≤ δ}.indicator
          (fun p : ℝ × ℝ => (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp p.1) p.2) ^ 2)
      from by
        funext p
        by_cases hp : |Real.log z - p.1| ≤ δ <;>
          simp [Set.indicator, hp]]
  exact haesm.indicator hS

end Work.FTS.EllSol.EllPkgAux.MollDom
