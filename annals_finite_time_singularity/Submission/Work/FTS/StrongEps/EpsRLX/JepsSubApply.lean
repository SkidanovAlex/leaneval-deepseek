import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.DiffAux.Jeps_sub_eq_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX

open Work.FTS.StrongEps

/-- `J_ε` is additive in its argument: the difference of two mollifications is the
mollification of the difference.  Both sides are the `p`-integral of `Jker ρ ε p` against the
corresponding shifted values (`Jeps_eq_integral`), so the identity is the linearity of the
Bochner integral on `ℝ²`; the two integrands are continuous with compact support (the kernel
vanishes off the ball of radius `ε`). -/
theorem JepsSubApply (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsMollKernel ρ) {ε : ℝ}
    (hε : 0 < ε) {g h : Work.FTS.Galerkin.Fn}
    (hg : ContinuousOn (Function.uncurry g) Work.FTS.StrongEps.Quad)
    (hh : ContinuousOn (Function.uncurry h) Work.FTS.StrongEps.Quad) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.FTS.StrongEps.Jeps ρ ε g z θ - Work.FTS.StrongEps.Jeps ρ ε h z θ
      = Work.FTS.StrongEps.Jeps ρ ε (fun z θ => g z θ - h z θ) z θ := by
  -- rewrite all three occurrences of `J_ε` as `p`-integrals
  rw [Jeps_eq_integral ρ ε g hz hθ, Jeps_eq_integral ρ ε h hz hθ,
      Jeps_eq_integral ρ ε (fun z θ => g z θ - h z θ) hz hθ]
  -- the shift of the quadrant point stays in the (open) quadrant
  have hmem : ∀ p : ℝ × ℝ, (zShift z p.1, thShift θ p.2) ∈ Quad :=
    fun _ => ⟨zShift_pos hz, thShift_mem hθ⟩
  have hcont_g : Continuous fun p : ℝ × ℝ => g (zShift z p.1) (thShift θ p.2) := by
    simpa only [Function.comp_def, Function.uncurry] using
      hg.comp_continuous (continuous_shift_pair z θ) hmem
  have hcont_h : Continuous fun p : ℝ × ℝ => h (zShift z p.1) (thShift θ p.2) := by
    simpa only [Function.comp_def, Function.uncurry] using
      hh.comp_continuous (continuous_shift_pair z θ) hmem
  -- both integrands are continuous with compact support, hence Bochner-integrable
  have hA : Integrable fun p : ℝ × ℝ => Jker ρ ε p * g (zShift z p.1) (thShift θ p.2) :=
    ((Jker_continuous hρ ε).mul hcont_g).integrable_of_hasCompactSupport
      (Jker_hasCompactSupport hρ hε).mul_right
  have hB : Integrable fun p : ℝ × ℝ => Jker ρ ε p * h (zShift z p.1) (thShift θ p.2) :=
    ((Jker_continuous hρ ε).mul hcont_h).integrable_of_hasCompactSupport
      (Jker_hasCompactSupport hρ hε).mul_right
  -- integrate the pointwise difference
  rw [← integral_sub hA hB]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  ring

end Work.FTS.StrongEps.EpsRLX
