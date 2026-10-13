import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.StrongEps.LocUnif.mixed_partials_of_smoothOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.StrongEps

/-- Additivity of the mixed operator `D_z^j D_θ^i` on the open quadrant, for data that are
`C^∞` on the (open) quadrant.

This is the instance of the general additivity `Work.FTS.EllipticEst.SmoothOpen.mixed_add`
for the raw hypothesis shape `∀ n, ContDiffOn ℝ n (Function.uncurry ·) Q0` used by the
downstream statements; the two shapes are equivalent by
`Work.FTS.EllipticEst.smoothOpen_iff_forall`.

(Note: `open scoped Real` is needed for the `π` of the `Set.Ioo 0 (π / 2)` hypothesis to be
`Real.pi`, matching `Work.FTS.EllipticEst.Q0`; without it `π` would be auto-bound as an
arbitrary real.) -/
theorem mixed_add {j i : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.mixed j i (fun z' θ' => f z' θ' + g z' θ') z θ
      = Work.Spaces.mixed j i f z θ + Work.Spaces.mixed j i g z θ :=
  Work.FTS.EllipticEst.SmoothOpen.mixed_add
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).mpr hf)
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall g).mpr hg)
    j i z θ hz hθ.1 hθ.2

end Work.FTS.StrongEps
