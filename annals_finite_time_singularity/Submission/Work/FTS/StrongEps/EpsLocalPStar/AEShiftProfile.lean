import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

/-- **Measurability of the shifted profile.**  If `f` is smooth on the open quadrant
(`Work.FTS.EllipticEst.SmoothOpen f`, i.e. `ContDiffOn ℝ smoothOrder (uncurry f) (Ioi 0 ×ˢ Ioo 0 (π/2))`),
then for `z > 0` and `θ ∈ (0,π/2)` the function
`p ↦ f (z * exp (-p.1)) (arctan (tan θ * exp (-p.2)))` is a.e. strongly measurable on `ℝ²`.

Route: the shift `p ↦ (z * exp (-p.1), arctan (tan θ * exp (-p.2)))` is continuous, and for
`z > 0`, `θ ∈ (0,π/2)` it maps `ℝ²` into the open quadrant `Q0 = Ioi 0 ×ˢ Ioo 0 (π/2)`
(`z * exp (-p.1) > 0`, `0 < arctan (tan θ * exp (-p.2)) < π/2`), on which `uncurry f` is
continuous (`SmoothOpen` gives `ContDiffOn`, hence `ContinuousOn`).  Hence the composite is
continuous at every point (`ContinuousOn.comp_continuous` with the shift continuous), so it is
a.e. strongly measurable for Lebesgue measure.  No quasi-measure-preserving input is needed —
`Work.FTS.StrongEps.qmp_sPhi` lies in a module not imported here.
Declare the result in the namespace `Work.FTS.StrongEps.EpsLocalPStar`. -/
theorem AEShiftProfile {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi/2)) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => f (z * Real.exp (-p.1)) (Real.arctan (Real.tan θ * Real.exp (-p.2))))
      (MeasureTheory.volume : Measure (ℝ × ℝ)) := by
  -- `SmoothOpen f` is `C^∞` on the open quadrant, hence continuous there.
  have hcont : ContinuousOn (Function.uncurry f) Work.FTS.EllipticEst.Q0 := hso.continuousOn
  -- The shift `p ↦ (z * exp (-p.1), arctan (tan θ * exp (-p.2)))` is continuous.
  have hshift : Continuous (fun p : ℝ × ℝ =>
      (z * Real.exp (-p.1), Real.arctan (Real.tan θ * Real.exp (-p.2)))) := by
    fun_prop
  -- For `z > 0` and `θ ∈ (0,π/2)` it lands in the open quadrant.
  have hmaps : ∀ p : ℝ × ℝ,
      (z * Real.exp (-p.1), Real.arctan (Real.tan θ * Real.exp (-p.2))) ∈
        Work.FTS.EllipticEst.Q0 := by
    intro p
    rw [Work.FTS.EllipticEst.mem_Q0]
    refine ⟨mul_pos hz (Real.exp_pos _), ?_, Real.arctan_lt_pi_div_two _⟩
    rw [Real.arctan_pos]
    exact mul_pos (Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2) (Real.exp_pos _)
  -- Hence the composite is continuous everywhere, and a fortiori a.e. strongly measurable.
  have hcomp : Continuous (fun p : ℝ × ℝ =>
      f (z * Real.exp (-p.1)) (Real.arctan (Real.tan θ * Real.exp (-p.2)))) := by
    simpa [Function.comp_def, Function.uncurry, Prod.fst, Prod.snd] using
      hcont.comp_continuous hshift hmaps
  exact hcomp.aestronglyMeasurable

end Work.FTS.StrongEps.EpsLocalPStar
