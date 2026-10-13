import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.Algebra
import Submission.Work.Elliptic.bslOp_sinG

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

/-- Adding the singular term `G(z) sin 2θ` to a solution `Ψ` of `LΨ = F` produces a solution of
`LΨ̂ = F - (15/4) F_*(z) sin 2θ = orthSource F`, provided `G` solves
`α²z²G'' + α(5+α)zG' = (15/4)F_*`.

This is the algebraic heart of §'The singular term' (paper line 1013): the solvability
obstruction `F_*` of the source is exactly removed by the radial singular part of `Ψ`, leaving
the orthogonal right hand side `orthSource F` to which the `L²` elliptic theory applies. -/
theorem bslOp_sing_source (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) (hθ : Real.cos θ ≠ 0)
    (hΨ : ContDiffAt ℝ 2 (Function.uncurry Ψ) (z, θ))
    (hG : ContDiffAt ℝ 2 (Work.Elliptic.Gsing α F) z)
    (hsol : Work.Elliptic.bslOp α Ψ z θ = F z θ)
    (hGode : α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α F) z') z
        + α * (5 + α) * z * deriv (Work.Elliptic.Gsing α F) z
      = (15 / 4) * Work.Elliptic.Fstar F z) :
    Work.Elliptic.bslOp α (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)) z θ
      = Work.Elliptic.orthSource F z θ := by
  rw [bslOp_sinG α Ψ (Gsing α F) z θ hΨ hG hθ, hsol, hGode]
  simp only [orthSource]
  ring

end Work.Elliptic
