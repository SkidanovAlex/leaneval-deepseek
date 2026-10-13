/-
# `Work.FTS.PhiStar.Radial.radGreen_solves`

The mode-`m` radial Euler Green's function `radGreen` (`Radial/Defs.lean`) is *definitionally* the
function `radGreenI` of `Radial/radGreenIntended.lean`, for which the ODE identity is proved
(`radGreenI_solves`).  Hence the identity transfers verbatim.

The notation trap that made the *original* `Defs.lean` a different, wrong function (the body of
`∫ t in (0:ℝ)..z, ·` extends as far right as possible and had swallowed the second summand), the
machine-checked certificate of the mis-parse, and the counterexample are recorded in
`Radial/NOTES_radGreen_solves_parse_bug.md` and `Radial/radGreen_parse.lean`; `Radial/Defs.lean`
now carries the parenthesised (intended) definition.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.PhiStar.Radial.radGreenIntended

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Radial

set_option autoImplicit false

/-- **The radial Green's function solves the mode-`m` Euler equation.**  For `α > 0`, `m : ℕ` and a
continuous source `c` on `(0,∞)` with the four integrability conditions, the explicit decaying
solution `radGreen α m c` satisfies `-α²z²a'' - α(5+α)z a' + λ_m a = c` at every `z > 0`. -/
theorem radGreen_solves {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1))
    (h0' : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) :
    ∀ z, 0 < z →
      -α ^ 2 * z ^ 2 * deriv (deriv (radGreen α m c)) z
        - α * (5 + α) * z * deriv (radGreen α m c) z
        + lamR m * radGreen α m c z = c z := by
  have hfun : radGreen α m c = radGreenI α m c := rfl
  have h := radGreenI_solves (α := α) hα m hc h0 h0' hinf
  simpa only [hfun] using h

end Work.FTS.PhiStar.Radial
