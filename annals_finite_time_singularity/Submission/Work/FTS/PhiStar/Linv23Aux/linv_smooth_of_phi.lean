/-
# `Work.FTS.PhiStar.Linv23Aux.linv_smooth_of_phi` — smoothness of `Linv` from that of its
primitive

`Linv_eq` (`Linv23Aux/Defs.lean`) writes `Linv h` as

`linv h θ = -((sin² θ cos³ θ)⁻¹ * LinvPhi h θ)`.

On `(0, π/2)` the weight `(sin² θ cos³ θ)⁻¹` is `C^∞` (its denominator is strictly positive
there), so smoothness of `LinvPhi h` transfers to `Linv h` by the algebraic closure of
`ContDiffOn`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.PhiStar.Linv23Aux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Linv23Aux

set_option autoImplicit false

/-- The `σ`-normalising weight `(sin² θ cos³ θ)⁻¹` is `C^∞` on `(0, π/2)`. -/
theorem contDiffOn_inv_sinSq_cosCu :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => (Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹) (Set.Ioo 0 (Real.pi / 2)) := by
  refine ContDiffOn.inv ?_ ?_
  · exact ((Real.contDiff_sin.contDiffOn).pow 2).mul ((Real.contDiff_cos.contDiffOn).pow 3)
  · intro x hx
    have hs : Real.sin x ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2, Real.pi_pos]))
    have hc : Real.cos x ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩)
    exact mul_ne_zero (pow_ne_zero 2 hs) (pow_ne_zero 3 hc)

/-- `Linv h` is `C^∞` on `(0, π/2)` as soon as the primitive `LinvPhi h` is. -/
theorem linv_contDiffOn_of_phi {h : ℝ → ℝ}
    (hPhi : ContDiffOn ℝ Work.Stability.smoothOrder (LinvPhi h)
      (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Linv h) (Set.Ioo 0 (Real.pi / 2)) :=
  ContDiffOn.congr ((contDiffOn_inv_sinSq_cosCu.mul hPhi).neg)
    (fun x _ => Linv_eq_phi h x)

end Work.FTS.PhiStar.Linv23Aux
