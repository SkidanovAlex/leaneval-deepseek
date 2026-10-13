import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Endpt

/-- Slicing a jointly `C^m` function in the second variable: if `uncurry Ψ` is `C^m` on the
open half-strip `(0,∞) × (0,π/2)` and `z > 0`, then every `θ`-slice `θ' ↦ Ψ z θ'` is `C^m`
on `(0,π/2)`.  (The corresponding Mathlib-free statement for the `z`-slice is
`Work.FTS.H2.contDiffOn_zslice_of_uncurry`.) -/
theorem contDiffOn_slice_of_uncurry {Ψ : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z) (m : ℕ)
    (hsm : ContDiffOn ℝ m (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ m (fun θ' => Ψ z θ') (Set.Ioo 0 (Real.pi / 2)) := by
  have hphi : ContDiffOn ℝ m (fun θ' : ℝ => ((z, θ') : ℝ × ℝ)) (Set.Ioo 0 (Real.pi / 2)) := by
    fun_prop
  have hcomp := hsm.comp hphi (fun θ' hθ' => ⟨hz, hθ'⟩)
  simpa [Function.comp_def, Function.uncurry] using hcomp

theorem slice_regularity_of_uncurry {Ψ : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hsm : ∀ m : ℕ, ContDiffOn ℝ m (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ 2 (fun θ' => Ψ z θ') (Set.Ioo 0 (Real.pi / 2))
      ∧ ContinuousOn (deriv (fun θ' => Ψ z θ')) (Set.Ioo 0 (Real.pi / 2))
      ∧ ContinuousOn (deriv (deriv (fun θ' => Ψ z θ'))) (Set.Ioo 0 (Real.pi / 2)) := by
  have h2 := contDiffOn_slice_of_uncurry hz 2 (hsm 2)
  have h3 := contDiffOn_slice_of_uncurry hz 3 (hsm 3)
  refine ⟨h2, h2.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num), ?_⟩
  have h1 : ContDiffOn ℝ 1 (deriv (fun θ' => Ψ z θ')) (Set.Ioo 0 (Real.pi / 2)) :=
    h3.deriv_of_isOpen isOpen_Ioo (by norm_num)
  exact h1.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)

end Work.FTS.EllipticEst.Endpt
