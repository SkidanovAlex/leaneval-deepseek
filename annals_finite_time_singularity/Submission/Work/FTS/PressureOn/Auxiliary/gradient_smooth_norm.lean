import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Gradient.Basic
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Auxiliary

/-- For a function `u` on `ℝ³` which is `C^∞`, its gradient `∇u = (toDual ℝ ℝ³).symm ∘ fderiv ℝ u`
is again `C^∞` (in every finite order), and its pointwise norm equals the operator norm of the
Fréchet derivative `fderiv ℝ u x` (the Fréchet–Riesz isometry `toDual ℝ ℝ³`). -/
theorem gradient_smooth_norm (u : EuclideanSpace ℝ (Fin 3) → ℝ) (hu : ∀ n : ℕ, ContDiff ℝ n u) :
    (∀ n : ℕ, ContDiff ℝ n (fun x => gradient u x)) ∧
      (∀ x, ‖gradient u x‖ = ‖fderiv ℝ u x‖) := by
  constructor
  · -- `∇u = (toDual ℝ ℝ³).symm ∘ fderiv ℝ u`; the derivative of a `C^{n+1}` function is `C^n`
    -- (`contDiff_succ_iff_fderiv`), and composing with a continuous linear isometry preserves the
    -- order of smoothness.
    intro n
    have hfd : ContDiff ℝ n (fderiv ℝ u) :=
      ((contDiff_succ_iff_fderiv (𝕜 := ℝ) (f := u) (n := (n : WithTop ℕ∞))).mp
        (hu (n + 1))).2.2
    have hcomp : ContDiff ℝ n
        ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm ∘ (fderiv ℝ u)) :=
      (LinearIsometryEquiv.contDiff _).comp hfd
    simpa [gradient, Function.comp_def] using hcomp
  · -- `gradient` is the inverse of the linear isometry equivalence `toDual ℝ ℝ³`, hence
    -- norm-preserving.
    intro x
    exact LinearIsometryEquiv.norm_map
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm (fderiv ℝ u x)

end Work.FTS.PressureOn.Auxiliary
