import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

/-- Integral of `(b - u) ^ (-p)` over `[θ, t]`, for `θ ≤ t < b` and `1 < p`.
The antiderivative is `u ↦ (b - u) ^ (1 - p) / (p - 1)`, whose derivative is `(b - u) ^ (-p)`. -/
theorem integral_sub_rpow_neg {b p t θ : ℝ} (hθt : θ ≤ t) (htb : t < b) (hp : 1 < p) :
    ∫ u in θ..t, (b - u) ^ (-p) = ((b - t) ^ (1 - p) - (b - θ) ^ (1 - p)) / (p - 1) := by
  -- On `[θ, t]` the base `b - u` is strictly positive.
  have hbt : 0 < b - t := by linarith
  have hbθ : 0 < b - θ := by linarith
  -- hence the shifted integration interval `[b - t, b - θ]` avoids `0`
  have h0mem : (0 : ℝ) ∉ Set.uIcc (b - t) (b - θ) := by
    intro h
    rw [Set.mem_uIcc] at h
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
  -- substitute `u ↦ b - u`
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (-p)) b]
  -- evaluate `∫ x in (b-t)..(b-θ), x ^ (-p)` with the power rule
  rw [integral_rpow (Or.inr ⟨by linarith, h0mem⟩)]
  -- clean up the arithmetic: `(-p + 1) = -(p - 1)`
  have h1 : (-p + 1 : ℝ) = 1 - p := by ring
  rw [h1, show (1 : ℝ) - p = -(p - 1) by ring, div_neg, ← neg_div, neg_sub]

end Work.FTS.EllipticEst.remov
