import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Endpt

theorem Lzero1_mul_sinCos2_eq {u : ℝ → ℝ} {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hdu : DifferentiableAt ℝ u θ) :
    Work.FTS.EllipticEst.Lzero1 u θ * Work.Elliptic.sinCos2 θ
      = -(deriv (deriv u) θ) * Work.Elliptic.sinCos2 θ
        + Real.sin θ * u θ + (Real.sin θ) ^ 2 * Real.cos θ * deriv u θ
        - 6 * u θ * Work.Elliptic.sinCos2 θ := by
  have hcos : Real.cos θ ≠ 0 := by
    have h : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    linarith
  have hdtan : DifferentiableAt ℝ Real.tan θ := Real.differentiableAt_tan.2 hcos
  -- product rule for `θ ↦ tan θ * u θ`
  have hdprod : deriv (fun t => Real.tan t * u t) θ
      = 1 / Real.cos θ ^ 2 * u θ + Real.tan θ * deriv u θ := by
    change deriv (Real.tan * u) θ = 1 / Real.cos θ ^ 2 * u θ + Real.tan θ * deriv u θ
    rw [deriv_mul hdtan hdu, Real.deriv_tan]
  rw [Work.FTS.EllipticEst.Lzero1, Work.Elliptic.sinCos2, hdprod, Real.tan_eq_sin_div_cos]
  field_simp
  ring

end Work.FTS.EllipticEst.Endpt
