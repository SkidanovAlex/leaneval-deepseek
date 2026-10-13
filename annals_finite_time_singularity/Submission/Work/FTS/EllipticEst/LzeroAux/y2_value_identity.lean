import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.LzeroAux

theorem y2_value_identity : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∀ F : ℝ,
    -4 * Real.sin (2 * θ) * F
        + 2 * Real.cos (2 * θ) * (-(1 / (Real.cos θ * Real.sin (2 * θ) ^ 2)))
        + (2 * Real.cos θ * Real.cos (2 * θ) - Real.sin θ * Real.sin (2 * θ))
            / (Real.cos θ * Real.sin (2 * θ)) ^ 2
      = -4 * Real.sin (2 * θ) * F - Real.sin θ / (Real.cos θ ^ 2 * Real.sin (2 * θ)) := by
  intro θ hθ F
  -- Positivity of the denominators on `(0, π/2)`.
  have hpi := Real.pi_pos
  have hcos : Real.cos θ ≠ 0 := by
    have h := Real.cos_pos_of_mem_Ioo (show θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith [hθ.1, hpi], by linarith [hθ.2, hpi]⟩)
    positivity
  have hsin : Real.sin θ ≠ 0 := by
    have h := Real.sin_pos_of_mem_Ioo (show θ ∈ Set.Ioo 0 Real.pi from
      ⟨hθ.1, by linarith [hθ.2, hpi]⟩)
    positivity
  have hsin2 : Real.sin (2 * θ) ≠ 0 := by
    have h := Real.sin_pos_of_mem_Ioo (show 2 * θ ∈ Set.Ioo 0 Real.pi from
      ⟨by linarith [hθ.1], by linarith [hθ.2, hpi]⟩)
    positivity
  -- Reduce to the double-angle identities: after the rewrites everything is rational in
  -- `sin θ`, `cos θ` (the identity is one of the double-angle algebra).
  rw [Real.sin_two_mul θ, Real.cos_two_mul θ]
  field_simp
  ring

end Work.FTS.EllipticEst.LzeroAux
