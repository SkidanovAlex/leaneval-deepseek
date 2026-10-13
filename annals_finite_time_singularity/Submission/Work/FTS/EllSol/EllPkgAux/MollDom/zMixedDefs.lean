/-
# `Work.FTS.EllSol.EllPkgAux.MollDom.zMixedDefs` — the one-variable Schur operator of the
`z`-mollification

The `z`-mollification `zmoll G δ ε z θ = ∫ t, sKer δ (log z - t) * thMoll G ε (e^t) θ` is a
logarithmic convolution in the `z`-variable.  Its `D_z`-derivative replaces the kernel
`sKer δ` by its derivative `sKerd δ = deriv (sKer δ)`, and the operator which appears is

  `zSchur δ g z = ∫ t, sKerd δ (log z - t) * g (e^t)`,

applied to the angular slices: `W z s = zSchur δ (fun w => G w s) z`,
`Y z s = zSchur δ (fun w => pth G w s) z`, `zSchur δ (fun w => pth (pth G) w s) z`, …

This file only fixes the notation; the analytic facts about it live in the sibling modules.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

set_option autoImplicit false

/-- The one-variable logarithmic Schur operator of the kernel `sKerd δ`:

  `zSchur δ g z = ∫ t, sKerd δ (log z - t) * g (exp t)`.

It is the operator obtained by moving the `D_z`-derivative of the `z`-mollification onto the
kernel, applied to a single angular slice `g` (i.e. `g w = G w s` for a fixed `s`). -/
def zSchur (δ : ℝ) (g : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ t : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t) * g (Real.exp t)

end Work.FTS.EllSol.EllPkgAux.MollDom
