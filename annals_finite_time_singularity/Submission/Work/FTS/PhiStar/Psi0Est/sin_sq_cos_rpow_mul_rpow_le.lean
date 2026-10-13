import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Psi0Est

/-- Elementary bound on the model function of the endpoint analysis of `ψ`:
for `0 < α ≤ 1/4` and `θ ∈ (0, π/2)`,
`sin²θ · cos^{2α/3}θ · (sin 2θ)^{-α/5} ≤ 1`.

Since `sin 2θ = 2 sin θ cos θ`, the left-hand side equals
`2^{-α/5} · sin^{2-α/5}θ · cos^{2α/3-α/5}θ`, a product of three factors each in `[0,1]`
(here `2 - α/5 ≥ 0` and `2α/3 - α/5 = 7α/15 ≥ 0`). -/
theorem sin_sq_cos_rpow_mul_rpow_le (α θ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3) * (Real.sin (2 * θ)) ^ (-(α / 5)) ≤ 1 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hθlt : θ < Real.pi := lt_trans hθ.2 (by linarith [hπ])
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθlt
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hπ, hθ.1], hθ.2⟩
  have hs1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hb : 0 < α / 5 := by linarith
  have hb2 : 0 ≤ 2 - α / 5 := by linarith
  have hab : 0 ≤ 2 * α / 3 - α / 5 := by linarith
  have htwo : (0 : ℝ) ≤ 2 := by norm_num
  -- split the `sin 2θ`-factor
  have e1 : (2 * Real.sin θ * Real.cos θ) ^ (-(α / 5))
      = 2 ^ (-(α / 5)) * Real.sin θ ^ (-(α / 5)) * Real.cos θ ^ (-(α / 5)) := by
    rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2 * Real.sin θ) (le_of_lt hc),
      Real.mul_rpow htwo (le_of_lt hs)]
  -- turn the natural power on `sin θ` into a real power
  have e2 : Real.sin θ ^ 2 = Real.sin θ ^ (2 : ℝ) := (Real.rpow_natCast (Real.sin θ) 2).symm
  have e3 : Real.sin θ ^ (2 : ℝ) * Real.sin θ ^ (-(α / 5)) = Real.sin θ ^ (2 - α / 5) :=
    (Real.rpow_add hs (2 : ℝ) (-(α / 5))).symm
  have e4 : Real.cos θ ^ (2 * α / 3) * Real.cos θ ^ (-(α / 5))
      = Real.cos θ ^ (2 * α / 3 - α / 5) :=
    (Real.rpow_add hc (2 * α / 3) (-(α / 5))).symm
  -- the exact value of the left-hand side
  have hkey : Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3) * (Real.sin (2 * θ)) ^ (-(α / 5))
      = 2 ^ (-(α / 5)) * Real.sin θ ^ (2 - α / 5) * Real.cos θ ^ (2 * α / 3 - α / 5) := by
    rw [Real.sin_two_mul, e1]
    calc Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3) *
            (2 ^ (-(α / 5)) * Real.sin θ ^ (-(α / 5)) * Real.cos θ ^ (-(α / 5)))
        = (Real.sin θ ^ (2 : ℝ) * Real.sin θ ^ (-(α / 5))) *
            (Real.cos θ ^ (2 * α / 3) * Real.cos θ ^ (-(α / 5))) * 2 ^ (-(α / 5)) := by
          rw [e2]; ring
      _ = Real.sin θ ^ (2 - α / 5) * Real.cos θ ^ (2 * α / 3 - α / 5) * 2 ^ (-(α / 5)) := by
          rw [e3, e4]
      _ = 2 ^ (-(α / 5)) * Real.sin θ ^ (2 - α / 5) * Real.cos θ ^ (2 * α / 3 - α / 5) := by
          ring
  rw [hkey]
  -- the three factors are each `≤ 1` and nonnegative
  have hbnd1 : (2 : ℝ) ^ (-(α / 5)) ≤ 1 := by
    rw [Real.rpow_neg (x := (2 : ℝ)) htwo (α / 5)]
    exact inv_le_one_of_one_le₀ (Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) (le_of_lt hb))
  have hbnd2 : Real.sin θ ^ (2 - α / 5) ≤ 1 := Real.rpow_le_one (le_of_lt hs) hs1 hb2
  have hbnd3 : Real.cos θ ^ (2 * α / 3 - α / 5) ≤ 1 := Real.rpow_le_one (le_of_lt hc) hc1 hab
  have hBC : Real.sin θ ^ (2 - α / 5) * Real.cos θ ^ (2 * α / 3 - α / 5) ≤ 1 := by
    simpa using mul_le_mul hbnd2 hbnd3 (Real.rpow_nonneg (le_of_lt hc) _)
      (by norm_num : (0 : ℝ) ≤ 1)
  have := mul_le_mul hbnd1 hBC
    (mul_nonneg (Real.rpow_nonneg (le_of_lt hs) _) (Real.rpow_nonneg (le_of_lt hc) _))
    (by norm_num : (0 : ℝ) ≤ 1)
  linarith [this]

end Work.FTS.PhiStar.Psi0Est
