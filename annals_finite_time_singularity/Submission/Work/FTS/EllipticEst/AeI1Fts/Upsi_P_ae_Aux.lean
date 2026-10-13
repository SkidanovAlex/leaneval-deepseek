import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.Defs
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.N_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Auxiliaries for `Upsi_P_integrable_ae`

The pointwise identity behind the target `Work.FTS.EllipticEst.AeI1Fts.Upsi_P_integrable_ae`:
for a datum `u` smooth on the open quadrant, a `C²` function `ψ` and a point `(z,θ)` of the open
quadrant, the derivative of the slice `θ' ↦ U u z θ' * ψ θ'` is

  `deriv (U u z · * ψ) θ = V u z θ * ψ θ + U u z θ * deriv ψ θ`,

where `U u = z ∂_z u` and `V u = z ∂_z∂_θ u` (which coincides with `∂_θ (U u)` on the quadrant,
`Work.FTS.EllipticEst.AeI1Fts.slice_deriv_eq`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeI1Fts

set_option autoImplicit false

/-- The `θ`-slice `θ' ↦ U u z θ'` of `U u = z ∂_z u` is differentiable at every interior angle
(with derivative `V u z θ` there). -/
theorem differentiableAt_slice_U {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u)
    {z : ℝ} (hz : 0 < z) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    DifferentiableAt ℝ (fun θ' => U u z θ') θ := by
  have hle : (1 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder :=
    WithTop.coe_le_coe.mpr le_top
  have hcd : ContDiffOn ℝ 1 (fun θ' => U u z θ') (Set.Ioo 0 (Real.pi / 2)) :=
    (hS.Dz.curry_θ hz).of_le hle
  exact (hcd.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hθ)

/-- **Product rule for the slice `θ ↦ U u z θ * ψ θ`.** -/
theorem deriv_U_mul_eq {u : ℝ → ℝ → ℝ} {ψ : ℝ → ℝ}
    (hS : Work.FTS.EllipticEst.SmoothOpen u) (hψcd : ContDiff ℝ 2 ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun θ' => U u z θ' * ψ θ') θ
      = V u z θ * ψ θ + U u z θ * deriv ψ θ := by
  have hUdiff : DifferentiableAt ℝ (fun θ' => U u z θ') θ := differentiableAt_slice_U hS hz hθ
  have hψdiff : DifferentiableAt ℝ ψ θ :=
    (hψcd.differentiable (by norm_num)).differentiableAt
  have hprod : deriv (fun θ' => U u z θ' * ψ θ') θ
      = deriv (fun θ' => U u z θ') θ * ψ θ + U u z θ * deriv ψ θ :=
    deriv_mul hUdiff hψdiff
  rw [hprod, slice_deriv_eq hS hz hθ]

end Work.FTS.EllipticEst.AeI1Fts
