import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB25Aux

theorem axisD2_ident (f : ℝ → ℝ) {θ0 : ℝ} (hθ0 : θ0 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (h1 : DifferentiableAt ℝ f θ0) (h2 : DifferentiableAt ℝ (deriv f) θ0) :
    deriv (deriv f) θ0
      = deriv (fun s => deriv f s - Real.tan s * f s) θ0
        + Real.tan θ0 * (deriv f θ0 - Real.tan θ0 * f θ0)
        + f θ0 * (1 + Real.sin θ0 ^ 2) / Real.cos θ0 ^ 2 := by
  have hcos_pos : 0 < Real.cos θ0 :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ0.1], hθ0.2⟩
  have hcos : Real.cos θ0 ≠ 0 := ne_of_gt hcos_pos
  have htan_diff : DifferentiableAt ℝ Real.tan θ0 := Real.differentiableAt_tan.mpr hcos
  have hmul : DifferentiableAt ℝ (fun s => Real.tan s * f s) θ0 := htan_diff.mul h1
  -- the product rule for `tan · f`
  have hA : deriv (fun s => Real.tan s * f s) θ0
      = 1 / Real.cos θ0 ^ 2 * f θ0 + Real.tan θ0 * deriv f θ0 := by
    change deriv (Real.tan * f) θ0 = 1 / Real.cos θ0 ^ 2 * f θ0 + Real.tan θ0 * deriv f θ0
    rw [deriv_mul htan_diff h1, Real.deriv_tan]
  -- the derivative of the bracket `deriv f - tan · f`
  have hderiv_g : deriv (fun s => deriv f s - Real.tan s * f s) θ0
      = deriv (deriv f) θ0 - (1 / Real.cos θ0 ^ 2 * f θ0 + Real.tan θ0 * deriv f θ0) := by
    change deriv (deriv f - fun s => Real.tan s * f s) θ0
      = deriv (deriv f) θ0 - (1 / Real.cos θ0 ^ 2 * f θ0 + Real.tan θ0 * deriv f θ0)
    rw [deriv_sub h2 hmul, hA]
  rw [hderiv_g, Real.tan_eq_sin_div_cos]
  field_simp
  ring

end Work.FTS_StreamBdry.SB25Aux
