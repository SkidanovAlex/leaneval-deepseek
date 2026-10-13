import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Mine.SlotDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT.Slot11

set_option autoImplicit false

/-- Every slice of a `SmoothOpen` function is differentiable on the open angular interval.
(A local copy of `Work.FTS.EllipticEst.Mine.differentiableAt_slice_of_smoothOpen`, so that the
shifted Step-4 estimate does not have to import the heavy `Mine/SrcDerivSlice` chain.) -/
theorem differentiableAt_slice_of_smoothOpen {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) {z : ℝ} (hz : 0 < z)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    DifferentiableAt ℝ (fun t => g z t) θ := by
  have hcd := hg.curry_θ hz
  have hd : DifferentiableOn ℝ (fun t => g z t) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hcd.differentiableOn (by simp [Work.Stability.smoothOrder])
  exact hd.differentiableAt (isOpen_Ioo.mem_nhds hθ)

/-- The angular weight `sin(2θ)^{2-γ}` is measurable (it is continuous for `γ ≤ 3/2`). -/
theorem measurable_sig2 {γ : ℝ} (hγ2 : γ ≤ 3 / 2) :
    Measurable fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) (2 - γ) := by
  have hq : 0 ≤ 2 - γ := by linarith
  have h1 : Continuous fun x : ℝ => x ^ (2 - γ) := Real.continuous_rpow_const hq
  have h2 : Continuous fun θ : ℝ => Real.sin (2 * θ) := by fun_prop
  exact (h1.comp h2).measurable

/-- `sin(2θ)^{2-γ} ≤ 1` on `Iθ`, for `γ ≤ 3/2`. -/
theorem sig2_le_one_of_mem_Iθ {γ : ℝ} (hγ2 : γ ≤ 3 / 2) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Real.rpow (Real.sin (2 * θ)) (2 - γ) ≤ 1 := by
  refine Real.rpow_le_one ?_ (Real.sin_le_one _) (by linarith)
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

end Work.FTS.EllipticEst.TT.Slot11
