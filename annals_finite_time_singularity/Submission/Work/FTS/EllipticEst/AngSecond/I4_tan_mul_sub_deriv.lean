import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Submission.Work.FTS.EllipticEst.AngSecond.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngSecond

/-- The pointwise identity of the `I₄` computation (Elgindi, Annals 194 (3) 2021, Step 2 of
`prop:H2`): on the open quadrant `0 < θ < π/2`,
`∂_θ(tan θ · u) - u = sin θ · ∂_θ(u / cos θ)`.
Continuity of the two sides on the closed quadrant is *not* asserted (the identity is used
only inside the open interval). -/
theorem I4_tan_mul_sub_deriv (u : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hu : DifferentiableAt ℝ u θ) :
    deriv (fun θ' => Real.tan θ' * u θ') θ - u θ
      = Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ := by
  have hcos : Real.cos θ ≠ 0 := by
    have h : θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo h)
  have htan : DifferentiableAt ℝ Real.tan θ := Real.differentiableAt_tan.mpr hcos
  rw [show deriv (fun θ' => Real.tan θ' * u θ') θ = deriv (Real.tan * u) θ from rfl,
    deriv_mul htan hu,
    show deriv (fun θ' => u θ' / Real.cos θ') θ = deriv (u / Real.cos) θ from rfl,
    deriv_div hu Real.differentiableAt_cos hcos,
    Real.deriv_tan θ, Real.deriv_cos, Real.tan_eq_sin_div_cos]
  field_simp
  linear_combination -(u θ) * Real.sin_sq_add_cos_sq θ

end Work.FTS.EllipticEst.AngSecond
