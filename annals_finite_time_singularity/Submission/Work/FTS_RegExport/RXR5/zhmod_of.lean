import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.RegPkgGal.Der.Lib.lip_of_bounded_deriv
import Submission.Work.FTS.RegPkgGal.Der.Lib.holder_of_lipschitz_of_bounded

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXR5

theorem zhmod_of {α S M B : ℝ} {h : ℝ → ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hdiff : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ θ ∈ Work.Spaces.Iθ, ∀ x ∈ Set.Ioi (0:ℝ),
      DifferentiableAt ℝ (fun z' => h z' θ τ) x)
    (hdb : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ θ ∈ Work.Spaces.Iθ, ∀ x ∈ Set.Ioi (0:ℝ),
      |deriv (fun z' => h z' θ τ) x| ≤ M)
    (hc0 : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ θ ∈ Work.Spaces.Iθ,
      ContinuousAt (fun z' => h z' θ τ) 0)
    (hb : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 ≤ z → |h z θ τ| ≤ B) :
    ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' →
      |h z θ τ - h z' θ τ| ≤ max M (2 * B) * |z - z'| ^ α := by
  intro τ hτ θ hθ z z' hz hz'
  -- The mean value theorem on `(0, ∞)` makes each `θ`-slice `M`-Lipschitzian on `[0, ∞)`:
  -- differentiability is assumed on the open half-line and only continuity is needed at `0`.
  have hlip : ∀ y y' : ℝ, 0 ≤ y → 0 ≤ y' →
      |h y θ τ - h y' θ τ| ≤ M * |y - y'| :=
    Work.FTS.RegPkgGal.Der.Lib.lip_of_bounded_deriv hM
      (fun x hx => hdiff τ hτ θ hθ x hx)
      (fun x hx => hdb τ hτ θ hθ x hx)
      (hc0 τ hτ θ hθ)
  -- Interpolate between the Lipschitz bound (small distances) and the sup bound (large ones).
  exact Work.FTS.RegPkgGal.Der.Lib.holder_of_lipschitz_of_bounded hα hα1 hM hB hlip
    (fun y hy => hb τ hτ θ hθ y hy) z z' hz hz'

end Work.FTS_RegExport.RXR5
