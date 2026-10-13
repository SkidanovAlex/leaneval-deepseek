import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Submission.Work.EllipticEst.InteriorRegularity.Q0.Defs
import Submission.Work.EllipticEst.InteriorRegularity.Strip
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.InteriorRegularity.Q0

theorem smoothOn_Gf {α : ℝ} (hα : 0 < α) {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) :
    ∀ n : ℕ, ContDiffOn ℝ n
      (fun x : E2 => (Work.EllipticEst.InteriorRegularity.Q0.Gf α F x : ℂ))
      Work.EllipticEst.InteriorRegularity.stripE := by
  intro n
  -- The un-indicated transported source is `C^n` on the strip, by composition: the map
  -- `x ↦ (exp (α x 0), x 1)` sends the strip into the open quadrant, where `F` is `C^∞`.
  have hcomp : ContDiffOn ℝ n
      (fun x : E2 => Function.uncurry F (Real.exp (α * x 0), x 1)) stripE := by
    refine (hF.forall n).comp ?_ ?_
    · fun_prop
    · intro x hx
      exact ⟨Real.exp_pos _, hx.1, hx.2⟩
  -- multiply by the smooth weight and push through the real-to-complex coercion
  have hmul : ContDiffOn ℝ n
      (fun x : E2 => wt α x * Function.uncurry F (Real.exp (α * x 0), x 1)) stripE :=
    ((wt_contDiff α n).contDiffOn).mul hcomp
  have hc : ContDiffOn ℝ n
      (fun x : E2 =>
        ((wt α x * Function.uncurry F (Real.exp (α * x 0), x 1) : ℝ) : ℂ)) stripE :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hmul
  -- on the strip the indicator is the identity
  refine hc.congr ?_
  intro x hx
  simp only [Gf, Function.uncurry, Set.indicator_of_mem hx]

end Work.EllipticEst.InteriorRegularity.Q0
