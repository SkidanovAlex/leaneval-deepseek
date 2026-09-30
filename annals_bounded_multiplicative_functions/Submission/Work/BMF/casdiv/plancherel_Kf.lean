import Mathlib
import Submission.Work.BMF.halasz_defs
import Submission.Work.BMF.halasz_plancherel
import Submission.Work.BMF.halasz_plancherel_defs
import Submission.Work.BMF.integral_dirSum_sq
import Submission.Work.BMF.tendsto_integral_KfN
import Submission.Work.BMF.tendsto_integral_dirSum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Mellin–Plancherel for `Kf`, in the `casdiv` namespace

`Work.BMF.halasz_plancherel` (proved in `Submission/Work/BMF/halasz_plancherel.lean`)
establishes exactly the Mellin–Plancherel / Parseval identity for the summatory function
`Kf f t = Σ_{n ≤ t} f n log n` of a `1`-bounded coefficient sequence:

`∫_0^∞ ‖Kf f t‖² / t^{3+2α} dt = (1/2π) ∫_ℝ ‖Kser f (1+α+iτ)‖² / ‖1+α+iτ‖² dτ`  (`α > 0`),

where `Kser f s = Σ_n f n (log n) n^{-s}` is the corresponding Dirichlet series.

This file restates it in `Work.BMF.casdiv` so that the downstream argument
(`Work.BMF.casdiv.series_tau`, bounding `∫_1^x ‖Kf f t‖² / t^{3+2α} dt` by
`min(exp 2Wsup, ...)`-type quantities) can consume the identity without leaving the
namespace it works in.  The identity itself is the Cauchy/Lorentzian Fourier-pair plus
dominated-convergence computation carried out across

* `Work.BMF.integral_KfN_sq`      (truncated left hand side),
* `Work.BMF.integral_dirSum_sq`   (truncated right hand side),
* `Work.BMF.tendsto_integral_KfN` / `Work.BMF.tendsto_integral_dirSum` (limits).
-/

namespace Work.BMF.casdiv

/-- Mellin–Plancherel (Parseval) identity for `Kf f t = Σ_{n ≤ t} f n · log n`:
the `L²` norm of `Kf f` against the Mellin weight `t^{-(3+2α)}` on `(0,∞)` equals
`1/(2π)` times the `L²` norm of the Dirichlet series `Kser f` on the line `1 + α + iℝ`,
with the Mellin measure `‖s‖^{-2}`. -/
theorem plancherel_Kf (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) {α : ℝ} (hα : 0 < α) :
    (∫ t in Set.Ioi (0 : ℝ), ‖Kf f t‖ ^ 2 / t ^ (3 + 2 * α))
      = (1 / (2 * Real.pi)) *
        (∫ τ : ℝ, ‖Kser f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 /
          ‖((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I‖ ^ 2) :=
  Work.BMF.halasz_plancherel f hb α hα

end Work.BMF.casdiv
