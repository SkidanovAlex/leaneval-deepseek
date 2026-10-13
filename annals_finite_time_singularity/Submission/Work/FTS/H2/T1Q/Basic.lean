import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.H2.Defs
import Submission.Work.FTS.H2.T1Defs
import Submission.Work.FTS.H2.RegQDefs
import Submission.Work.FTS.H2.HQ.Glue

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

/-! ## the interior angular slice supremum -/

/-- `supAbsThO u z` is the supremum of `|u z θ|` over `θ ∈ (0,π/2)`, at the fixed radial
variable `z`.  This is the interior version of `Work.FTS.H2.supAbsTh` (which takes the
supremum over the *closed* interval `Iθ`): for `SmoothQuad` data the values on the boundary
lines `θ = 0, π/2` are unconstrained, so only the open interval is meaningful. -/
def supAbsThO (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ := sSup {y : ℝ | ∃ θ ∈ Set.Ioo 0 (π / 2), y = |u z θ|}

theorem abs_le_supAbsThO {u : ℝ → ℝ → ℝ} {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (h : BddAbove {y : ℝ | ∃ θ ∈ Set.Ioo 0 (π / 2), y = |u z θ|}) :
    |u z θ| ≤ supAbsThO u z :=
  le_csSup h ⟨θ, hθ, rfl⟩

theorem supAbsThO_le {u : ℝ → ℝ → ℝ} {z C : ℝ}
    (h : ∀ θ ∈ Set.Ioo 0 (π / 2), |u z θ| ≤ C) : supAbsThO u z ≤ C :=
  csSup_le ⟨|u z (π / 4)|, π / 4, ⟨by positivity, by linarith [Real.pi_pos]⟩, rfl⟩
    (fun y hy => by rcases hy with ⟨θ, hθ, rfl⟩; exact h θ hθ)

end Work.FTS.H2
