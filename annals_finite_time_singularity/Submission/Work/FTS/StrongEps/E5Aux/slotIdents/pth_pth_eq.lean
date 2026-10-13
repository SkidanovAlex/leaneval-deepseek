import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux.slotIdents

/-- Product rule for `∂_θ` applied to `sin(2·)·∂_θ g`, i.e. the derivative of the
`θ`-slice of `D_θ g = sin(2θ)·∂_θ g`:
`(sin(2·)·g')'(θ) = 2 cos(2θ)·g'(θ) + sin(2θ)·g''(θ)`
whenever `g` is `C²` at `θ`. -/
theorem deriv_sin_two_mul_deriv (g : ℝ → ℝ) (θ : ℝ) (hg : ContDiffAt ℝ 2 g θ) :
    deriv (fun θ' => Real.sin (2 * θ') * deriv g θ') θ
      = 2 * Real.cos (2 * θ) * deriv g θ
        + Real.sin (2 * θ) * deriv (fun θ' => deriv g θ') θ := by
  -- `g` is `C¹`, so `deriv g` is `C¹`, hence differentiable, with derivative `deriv (deriv g)`.
  have hg1 : ContDiffAt ℝ 1 (deriv g) θ := hg.derivWithin (by norm_num)
  have hd2 : DifferentiableAt ℝ (deriv g) θ := hg1.differentiableAt (by norm_num)
  have hD : HasDerivAt (deriv g) (deriv (deriv g) θ) θ := hasDerivAt_deriv_iff.mpr hd2
  -- `θ' ↦ sin(2θ')` has derivative `2 cos(2θ)`.
  have hS : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
    have h2 : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    have hh := HasDerivAt.comp θ (Real.hasDerivAt_sin (2 * θ)) h2
    simpa [Function.comp_def, mul_comm] using hh
  exact (hS.mul hD).deriv

/-- `∂_θ²u` expressed through the mixed operators: since `D_θ² = sin(2θ)²·∂_θ² + 2 sin(2θ) cos(2θ)·∂_θ`,
one recovers `∂_θ²u` from `D_θ²u` and `D_θu` by dividing by `sin(2θ)²`. -/
theorem pth_pth_eq {u : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ 2 (Function.uncurry u) (z, θ)) (hs : Real.sin (2 * θ) ≠ 0) :
    Work.Spaces.pth (Work.Spaces.pth u) z θ
      = (Work.Spaces.mixed 0 2 u z θ
          - 2 * Real.sin (2 * θ) * Real.cos (2 * θ)
              * (Work.Spaces.mixed 0 1 u z θ / Real.sin (2 * θ)))
        / (Real.sin (2 * θ)) ^ 2 := by
  -- The `θ`-slice `t ↦ u z t` is `C²` at `θ`.
  have hg : ContDiffAt ℝ 2 (fun t : ℝ => u z t) θ := by
    have hq : ContDiffAt ℝ 2 (fun t : ℝ => (z, t)) θ := by fun_prop
    simpa [Function.comp_def] using h.comp θ hq
  -- Unfold the operator definitions: everything is a statement about the slice `g = u z ·`,
  -- namely `g''(θ)` versus `(sin(2θ)·(sin(2·)g')'(θ) - 2 sin(2θ)cos(2θ)·g'(θ)) / sin(2θ)²`.
  show deriv (fun θ' => deriv (fun t : ℝ => u z t) θ') θ
    = (Real.sin (2 * θ)
          * deriv (fun θ' => Real.sin (2 * θ') * deriv (fun t : ℝ => u z t) θ') θ
        - 2 * Real.sin (2 * θ) * Real.cos (2 * θ)
            * (Real.sin (2 * θ) * deriv (fun t : ℝ => u z t) θ / Real.sin (2 * θ)))
      / (Real.sin (2 * θ)) ^ 2
  rw [deriv_sin_two_mul_deriv (fun t : ℝ => u z t) θ hg]
  field_simp
  ring

end Work.FTS.StrongEps.E5Aux.slotIdents
