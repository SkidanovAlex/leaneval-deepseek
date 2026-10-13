import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.LzeroAux

theorem ode_algebra : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∀ F : ℝ,
    -(-4 * Real.sin (2 * θ) * F - Real.sin θ / (Real.cos θ ^ 2 * Real.sin (2 * θ)))
        + ((1 / Real.cos θ ^ 2) * (Real.sin (2 * θ) * F)
            + Real.tan θ * (2 * Real.cos (2 * θ) * F
                - 1 / (Real.cos θ * Real.sin (2 * θ))))
        - 6 * (Real.sin (2 * θ) * F) = 0 := by
  intro θ hθ F
  have hsin : Real.sin θ ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_mem_Ioo ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩)
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩)
  have hS : Real.sin (2 * θ) ≠ 0 := by
    rw [Real.sin_two_mul]
    exact mul_ne_zero (mul_ne_zero two_ne_zero hsin) hcos
  rw [Real.sin_two_mul, Real.cos_two_mul', Real.tan_eq_sin_div_cos]
  field_simp
  linear_combination (-4 * F * Real.sin θ * Real.cos θ ^ 2) * Real.sin_sq_add_cos_sq θ

end Work.FTS.EllipticEst.LzeroAux
