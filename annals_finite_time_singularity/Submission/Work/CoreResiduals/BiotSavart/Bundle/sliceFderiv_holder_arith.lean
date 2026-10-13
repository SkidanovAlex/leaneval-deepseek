import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart.Bundle

/-- **The arithmetic of the single-slice Schauder estimate.**

For `0 < α < 1`, `C ≥ 0`, `δ ≥ 0` and any constant `Kv`, factor `δ ^ α` out of the four pieces of
the near-field Schauder bound:

`4C(4π/α)((3δ)^α + (2δ)^α) + 1024 C δ (4π (2δ)^{α-1}/(1-α)) + (C Kv + (4π/3)C) δ^α
  ≤ (4C(4π/α)(3^α + 2^α) + 1024 C (4π 2^{α-1}/(1-α)) + (C Kv + (4π/3)C)) δ^α`.

Uses `(3δ)^α = 3^α δ^α`, `(2δ)^α = 2^α δ^α`, and `δ (2δ)^{α-1} = 2^{α-1} δ^α` (both valid for
`δ = 0` as well, since `α > 0` makes `0^α = 0` and `α - 1 < 0` makes `0^{α-1} = 0`). -/
theorem sliceFderiv_holder_arith {α C δ Kv : ℝ} (hα : 0 < α) (hα1 : α < 1) (hC : 0 ≤ C)
    (hδ : 0 ≤ δ) :
    4 * C * (4 * Real.pi / α) * ((3 * δ) ^ α + (2 * δ) ^ α)
      + 1024 * C * δ * (4 * Real.pi * (2 * δ) ^ (α - 1) / (1 - α))
      + (C * Kv + (4 * Real.pi / 3) * C) * δ ^ α
    ≤ (4 * C * (4 * Real.pi / α) * ((3 : ℝ) ^ α + (2 : ℝ) ^ α)
        + 1024 * C * (4 * Real.pi * (2 : ℝ) ^ (α - 1) / (1 - α))
        + (C * Kv + (4 * Real.pi / 3) * C)) * δ ^ α := by
  -- `(3δ)^α = 3^α δ^α` and `(2δ)^α = 2^α δ^α`, valid for `δ ≥ 0`.
  have h3 : (3 * δ) ^ α = (3 : ℝ) ^ α * δ ^ α := by
    rw [Real.mul_rpow (by norm_num) hδ]
  have h2 : (2 * δ) ^ α = (2 : ℝ) ^ α * δ ^ α := by
    rw [Real.mul_rpow (by norm_num) hδ]
  -- `δ * δ^(α-1) = δ^α`, valid for `δ ≥ 0` because `1 + (α - 1) = α ≠ 0`.
  have hpow : δ * δ ^ (α - 1) = δ ^ α := by
    have h := Real.rpow_add' (x := δ) hδ (y := 1) (z := α - 1) (by linarith)
    rw [Real.rpow_one δ] at h
    rw [show (1 : ℝ) + (α - 1) = α by ring] at h
    exact h.symm
  -- `δ * (2δ)^(α-1) = 2^(α-1) * δ^α`, valid for `δ ≥ 0`.
  have hδmul : δ * (2 * δ) ^ (α - 1) = (2 : ℝ) ^ (α - 1) * δ ^ α := by
    rw [Real.mul_rpow (by norm_num) hδ]
    calc δ * ((2 : ℝ) ^ (α - 1) * δ ^ (α - 1))
        = (2 : ℝ) ^ (α - 1) * (δ * δ ^ (α - 1)) := by ring
      _ = (2 : ℝ) ^ (α - 1) * δ ^ α := by rw [hpow]
  rw [h3, h2]
  -- The middle term rewrites using `hδmul` after reassociating the product.
  have hmid : 1024 * C * δ * (4 * Real.pi * (2 * δ) ^ (α - 1) / (1 - α))
      = 1024 * C * (4 * Real.pi * (2 : ℝ) ^ (α - 1) / (1 - α)) * δ ^ α := by
    rw [show 4 * Real.pi * (2 * δ) ^ (α - 1) / (1 - α)
          = (4 * Real.pi / (1 - α)) * (2 * δ) ^ (α - 1) by ring]
    rw [show 1024 * C * δ * ((4 * Real.pi / (1 - α)) * (2 * δ) ^ (α - 1))
          = (1024 * C * (4 * Real.pi / (1 - α))) * (δ * (2 * δ) ^ (α - 1)) by ring]
    rw [hδmul]
    ring
  rw [hmid]
  exact le_of_eq (by ring)

end Work.CoreResiduals.BiotSavart.Bundle
