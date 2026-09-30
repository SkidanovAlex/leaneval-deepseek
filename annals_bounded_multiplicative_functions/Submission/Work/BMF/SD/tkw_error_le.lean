import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

/-- Elementary arithmetic estimate used in the proof of Theorem 1.3: under the
constraints `2 ≤ p`, `64/c₀ ≤ p`, `p ≤ Q` and `Q³ ≤ H`, we have
`2 * (H / p² + 2) ≤ (c₀ / 4) * (H / p)`. -/
theorem tkw_error_le (c₀ H Q : ℝ) (p : ℕ) (hc₀ : 0 < c₀)
    (hp2 : (2 : ℝ) ≤ (p : ℝ)) (hp64 : 64 / c₀ ≤ (p : ℝ))
    (hpQ : (p : ℝ) ≤ Q) (hQ3 : Q ^ 3 ≤ H) :
    2 * (H / (p : ℝ) ^ 2 + 2) ≤ (c₀ / 4) * (H / (p : ℝ)) := by
  have hp_pos : (0:ℝ) < (p:ℝ) := by linarith
  have hQ_ge : (0:ℝ) < Q := by linarith
  -- `p³ ≤ Q³ ≤ H`
  have hp3_le_Q3 : (p:ℝ)^3 ≤ Q^3 := by
    apply pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ (p:ℝ)) hpQ
  have hp3_le_H : (p:ℝ)^3 ≤ H := le_trans hp3_le_Q3 hQ3
  have hp3pos : (0:ℝ) < (p:ℝ)^3 := by positivity
  have hH_pos : (0:ℝ) < H := by linarith
  -- `H ≥ p²` (since `p ≥ 2`)
  have hHp2 : (p:ℝ)^2 ≤ H := by nlinarith [hp3_le_H, hp2]
  -- `c₀ * p ≥ 64` (since `0 < c₀`)
  have hcp : 64 ≤ c₀ * (p:ℝ) := by
    have := (div_le_iff₀ hc₀).mp hp64
    linarith [this]
  -- cleared form of the goal
  have hkey : 8*H + 16*(p:ℝ)^2 ≤ c₀ * H * (p:ℝ) := by nlinarith [hHp2, hcp, hH_pos, hp2]
  have h4p2 : (0:ℝ) < 4 * (p:ℝ)^2 := by positivity
  have e1 : (4*(p:ℝ)^2) * (2 * (H/(p:ℝ)^2 + 2)) = 8*H + 16*(p:ℝ)^2 := by
    field_simp
    ring
  have e2 : (4*(p:ℝ)^2) * ((c₀/4)*(H/(p:ℝ))) = c₀*H*(p:ℝ) := by
    field_simp
  have hmul : (4*(p:ℝ)^2) * (2 * (H/(p:ℝ)^2 + 2))
      ≤ (4*(p:ℝ)^2) * ((c₀/4)*(H/(p:ℝ))) := by
    rw [e1, e2]; exact hkey
  exact le_of_mul_le_mul_left hmul h4p2

end Work.BMF.SD
