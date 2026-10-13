import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.aeStronglyMeasurable_exp
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open scoped Real Topology
open MeasureTheory Set Filter

/-- The angular weight `thEta θ = sin(2θ)^{-η}` is continuous on the open angular interval
`(0, π/2)` (there `sin(2θ) > 0`, so the real power is a composition of continuous maps). -/
lemma continuousOn_thEta_Ioo :
    ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  show ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
    (Set.Ioo (0 : ℝ) (Real.pi / 2))
  exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn.rpow_const
    (fun θ hθ => Or.inl (ne_of_gt (Work.FTS.EllipticEst.sin_two_pos hθ)))

/-- **A.e. strong measurability of the windowed weighted `∂_θG`-square of the trace datum.**

`G` is `C^∞` on the open quadrant (first component of `TraceClass`), hence so is `∂_θG`, so the
uncurried `(z,θ) ↦ thEta θ · (∂_θG z θ)²` is continuous on the (open) quadrant `Q0`: `thEta` is
continuous on `(0, π/2)` where `sin(2θ) > 0`, and `∂_θG` is continuous there.  Composing with
the continuous map `p ↦ (exp p.1, p.2)`, whose image of the half strip
`ℝ × (0,π/2)` (a set of full measure for `volume.prod (volume.restrict Iθ)`, see
`aeStronglyMeasurable_exp`) lies in `Q0`, gives the unwindowed a.e. strong measurability.
Multiplying by the indicator of the measurable window `{p | |log z - p.1| ≤ δ}` (a closed slab
in the logarithm of the radius) gives the statement.

No hypothesis on `δ` or on the sign of `z` is needed: the window is a closed (possibly empty)
interval, and its indicator is measurable regardless. -/
theorem thSlice_window_aesm_pth (G : ℝ → ℝ → ℝ)
    (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G) (δ z : ℝ) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => if |Real.log z - p.1| ≤ δ then
        Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.pth G (Real.exp p.1) p.2) ^ 2 else 0)
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  -- the angular weight and the first angular derivative of the datum are continuous on `Q0`
  have hth : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.thEta p.2)
      Work.FTS.EllipticEst.Q0 :=
    continuousOn_thEta_Ioo.comp continuous_snd.continuousOn
      (fun p hp => (Set.mem_prod.mp hp).2)
  have hcont : ContinuousOn (Function.uncurry
      (fun z θ : ℝ => Work.FTS.EllipticEst.thEta θ * (Work.Spaces.pth G z θ) ^ 2))
      Work.FTS.EllipticEst.Q0 :=
    hth.mul (((hT.1.pth).continuousOn).pow 2)
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.FTS.EllipticEst.thEta p.2 *
        (Work.Spaces.pth G (Real.exp p.1) p.2) ^ 2)
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    aeStronglyMeasurable_exp
      (X := fun z θ : ℝ => Work.FTS.EllipticEst.thEta θ * (Work.Spaces.pth G z θ) ^ 2) hcont
  -- the window `{p | |log z - p.1| ≤ δ}` is measurable
  have hmeas : Measurable (fun p : ℝ × ℝ => |Real.log z - p.1|) :=
    (continuous_const.sub continuous_fst).abs.measurable
  have hS : MeasurableSet {p : ℝ × ℝ | |Real.log z - p.1| ≤ δ} :=
    measurableSet_Iic.preimage hmeas
  -- the windowed function is the indicator of the window applied to the unwindowed one
  rw [show (fun p : ℝ × ℝ => if |Real.log z - p.1| ≤ δ then
        Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.pth G (Real.exp p.1) p.2) ^ 2 else 0)
      = {p : ℝ × ℝ | |Real.log z - p.1| ≤ δ}.indicator
          (fun p : ℝ × ℝ => Work.FTS.EllipticEst.thEta p.2 *
            (Work.Spaces.pth G (Real.exp p.1) p.2) ^ 2)
      from by
        funext p
        by_cases hp : |Real.log z - p.1| ≤ δ <;>
          simp [Set.indicator, hp]]
  exact haesm.indicator hS

end Work.FTS.EllSol.EllPkgAux.MollDom
