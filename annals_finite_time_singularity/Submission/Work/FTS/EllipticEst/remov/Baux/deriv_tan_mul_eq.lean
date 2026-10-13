import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.DthIter_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.Baux

/-- The product rule for `θ ↦ tan θ · φ θ` on the open interval `(0, π/2)`, written with the
angular derivation `Lop φ = sin(2θ) ∂_θ φ`:

`(tan θ · φ θ)' = (1 + tan²θ) · (φ θ + (1/2) · sin(2θ) · φ'(θ))`.

The factor `1 + tan²θ = 1/cos²θ` is the derivative of `tan`, and
`(1/2)·(1 + tan²θ)·sin(2θ) = tan θ` because `sin(2θ) = 2 sin θ cos θ` and
`sin²θ + cos²θ = 1`. -/
theorem deriv_tan_mul_eq (φ : ℝ → ℝ) {V : Set ℝ} (hV : IsOpen V)
    (hVsub : V ⊆ Set.Ioo 0 (Real.pi / 2)) (hφ : ContDiffOn ℝ 1 φ V) :
    ∀ θ ∈ V, deriv (fun s => Real.tan s * φ s) θ
      = (1 + Real.tan θ ^ 2) * (φ θ + (1 / 2) * Work.Spaces.Lop φ θ) := by
  intro θ hθV
  have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := hVsub hθV
  have hcospos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
  have hcos : Real.cos θ ≠ 0 := ne_of_gt hcospos
  have hdφ : DifferentiableAt ℝ φ θ :=
    (hφ.contDiffAt (hV.mem_nhds hθV)).differentiableAt (by norm_num)
  have htan : HasDerivAt Real.tan (1 / Real.cos θ ^ 2) θ := Real.hasDerivAt_tan hcos
  have hmul : HasDerivAt (fun s => Real.tan s * φ s)
      ((1 / Real.cos θ ^ 2) * φ θ + Real.tan θ * deriv φ θ) θ :=
    htan.mul hdφ.hasDerivAt
  rw [hmul.deriv, Work.Spaces.Lop, Real.tan_eq_sin_div_cos θ, Real.sin_two_mul θ]
  field_simp
  ring_nf
  linear_combination -(φ θ + Real.cos θ * Real.sin θ * deriv φ θ) * Real.sin_sq_add_cos_sq θ

end Work.FTS.EllipticEst.remov.Baux
