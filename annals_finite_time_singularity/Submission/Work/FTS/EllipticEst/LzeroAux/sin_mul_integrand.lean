import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.LzeroSingDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.LzeroAux

/-- The integrand `LzeroSingIntegrand s = 1/(sin s · sin(2s)²)` of the singular solution of
`Lzero`, evaluated at `s = π/2 - θ`, is `1/(cos θ · sin(2θ)²)`; multiplying by `sin 2θ` gives
`1/(cos θ · sin 2θ)`.  This is the value of the Wronskian quotient `W/ sin(2θ)²` at the
singular endpoint (cf. the `sin(2θ)·∂LzeroSing - ∂(sin 2θ)·LzeroSing = -1/cos θ` certificate). -/
theorem sin_mul_integrand : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
    Real.sin (2 * θ) * Work.FTS.EllipticEst.LzeroSingIntegrand (Real.pi / 2 - θ)
      = 1 / (Real.cos θ * Real.sin (2 * θ)) := by
  intro θ hθ
  have hpi := Real.pi_pos
  -- `cos θ ≠ 0` and `sin (2θ) ≠ 0` on the open interval `(0, π/2)`
  have hcos : Real.cos θ ≠ 0 := by
    have h := Real.cos_pos_of_mem_Ioo (show θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith [hθ.1], by linarith [hθ.2]⟩)
    linarith
  have hsin : Real.sin (2 * θ) ≠ 0 := by
    have h := Real.sin_pos_of_mem_Ioo (show 2 * θ ∈ Set.Ioo (0 : ℝ) Real.pi from
      ⟨by linarith [hθ.1], by linarith [hθ.2]⟩)
    linarith
  -- the two reflection identities `sin (π/2 - θ) = cos θ` and `sin (π - 2θ) = sin 2θ`
  have hs1 : Real.sin (Real.pi / 2 - θ) = Real.cos θ := Real.sin_pi_div_two_sub θ
  have hs2 : Real.sin (2 * (Real.pi / 2 - θ)) = Real.sin (2 * θ) := by
    rw [show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring, Real.sin_pi_sub]
  simp only [Work.FTS.EllipticEst.LzeroSingIntegrand]
  rw [hs1, hs2]
  field_simp

end Work.FTS.EllipticEst.LzeroAux
