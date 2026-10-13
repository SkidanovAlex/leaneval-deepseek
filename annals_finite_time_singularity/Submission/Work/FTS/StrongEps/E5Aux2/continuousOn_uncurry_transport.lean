import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Coercivity.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux2

/-- **The angular transport `3 sin(2θ) ∂_θf/(1+z)` is jointly continuous on the open
quadrant.**

`Transport f z θ = 3 D_θf(z,θ)/(1+z)` is the product of the continuous factor
`3 sin(2θ)/(1+z)` with the angular partial `∂_θf`.  The latter is continuous on `Q0` as soon
as `f` is `C¹` there: on the open quadrant the slice derivative `∂_θf` agrees with the
Fréchet derivative of `uncurry f` applied to the direction `(0,1)`, and the Fréchet
derivative of a `C¹` function on an open set is continuous.  Combined with the stability of
`∂_θ` inside `SmoothOpen` (`SmoothOpen.pth`) this gives the claim for every `SmoothOpen f`. -/
theorem continuousOn_uncurry_transport {f : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.SmoothOpen f) :
    ContinuousOn (Function.uncurry (Work.Coercivity.Transport f)) Work.FTS.EllipticEst.Q0 := by
  have hpth : ContinuousOn (Function.uncurry (Work.Spaces.pth f)) Work.FTS.EllipticEst.Q0 :=
    (h.pth).continuousOn
  have hsin : ContinuousOn (fun p : ℝ × ℝ => 3 * Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 :=
    (continuous_const.mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_snd))).continuousOn
  have hden : ContinuousOn (fun p : ℝ × ℝ => 1 + p.1) Work.FTS.EllipticEst.Q0 :=
    (continuous_const.add continuous_fst).continuousOn
  have hne : ∀ p ∈ Work.FTS.EllipticEst.Q0, (1 + p.1) ≠ 0 := by
    intro p hp
    have hp1 := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
    exact ne_of_gt (by linarith)
  have hmain := (hsin.mul hpth).div hden hne
  refine hmain.congr ?_
  intro p hp
  obtain ⟨z, θ⟩ := p
  simp only [Function.uncurry_apply_pair, Work.Coercivity.Transport, Work.Spaces.Dth,
    Pi.mul_apply, Pi.div_apply]
  ring

end Work.FTS.StrongEps.E5Aux2
