import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.CoercivityFix.Assembly.AnsatzDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

set_option autoImplicit false

/-- `deriv` of a `C^∞`-function is `C^∞` (the `∞`-order instance of
`ContDiff.iterate_deriv`). -/
theorem contDiff_deriv_of {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ Work.Stability.smoothOrder ψ) :
    ContDiff ℝ Work.Stability.smoothOrder (deriv ψ) := by
  have h : ContDiff ℝ Work.Stability.smoothOrder (deriv^[1] ψ) :=
    ContDiff.iterate_deriv 1 hψ
  simpa using h



/-- `vth` preserves `C^∞`-smoothness. -/
theorem contDiff_vth {g : ℝ → ℝ} (hg : ContDiff ℝ Work.Stability.smoothOrder g) :
    ContDiff ℝ Work.Stability.smoothOrder (vth g) := by
  have hsin : ContDiff ℝ Work.Stability.smoothOrder (fun θ : ℝ => Real.sin (2 * θ)) :=
    Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)
  have := hsin.mul (contDiff_deriv_of hg)
  exact this

/-- `vthIter` preserves `C^∞`-smoothness. -/
theorem contDiff_vthIter (g : ℝ → ℝ) (hg : ContDiff ℝ Work.Stability.smoothOrder g)
    (i : ℕ) : ContDiff ℝ Work.Stability.smoothOrder (vthIter i g) := by
  induction i with
  | zero => simpa using hg
  | succ i ih => simpa [vthIter_succ] using contDiff_vth ih

theorem smoothOrder_ne_zero : Work.Stability.smoothOrder ≠ 0 := by
  simp [Work.Stability.smoothOrder]




end Work.FTS.CoercivityFix.Assembly
