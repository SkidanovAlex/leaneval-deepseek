import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- The head-truncation term `a^{-σ} + 2·(5 e⁴)(2+κ)` of the shift-difference series is
dominated by a multiple of `a^{-σ} + L^{6/7}` when `κ ≤ cvk^{-6/7} L^{6/7}`. -/
lemma v7chi_head_arith {cvk : ℝ} (hcvk0 : 0 < cvk) (hcvk1 : cvk ≤ 1) :
    ∃ B : ℝ, 0 < B ∧ ∀ (a σ L κ : ℝ), 0 < a → a ≤ 1 → 0 < σ → 1 ≤ L → 0 ≤ κ →
      κ ≤ cvk ^ (-(6 / 7 : ℝ)) * L ^ (6 / 7 : ℝ) →
      a ^ (-σ) + 2 * (Real.exp 4 * 5 * (2 + κ)) ≤ B * (a ^ (-σ) + L ^ (6 / 7 : ℝ)) := by
  -- The constant `B = 2·(e⁴·5·(2 + cvk^{-6/7}))` only needs to absorb the `κ`-part on the
  -- `L^{6/7}` scale, since `L^{6/7} ≥ 1` and `cvk^{-6/7} > 0` are both bounded below on the
  -- range `L ≥ 1`, `0 < cvk`, and the `a^{-σ}` term is absorbed by the factor `B ≥ 1`.
  refine ⟨2 * (Real.exp 4 * 5 * (2 + cvk ^ (-(6/7:ℝ)))), ?_, ?_⟩
  · have hCpos : 0 < cvk ^ (-(6/7:ℝ)) := Real.rpow_pos_of_pos hcvk0 _
    have h2C : 0 < 2 + cvk ^ (-(6/7:ℝ)) := by linarith
    positivity
  · intro a σ L κ ha ha1 hσ hL1 hκ0 hκ
    have hXnn : 0 ≤ a ^ (-σ) := le_of_lt (Real.rpow_pos_of_pos ha _)
    have hY1 : 1 ≤ L ^ (6/7:ℝ) := Real.one_le_rpow hL1 (by norm_num)
    have hCpos : 0 < cvk ^ (-(6/7:ℝ)) := Real.rpow_pos_of_pos hcvk0 _
    have hCnn : 0 ≤ cvk ^ (-(6/7:ℝ)) := le_of_lt hCpos
    -- `2 + κ ≤ (2 + cvk^{-6/7}) · L^{6/7}` since `κ ≤ cvk^{-6/7}·L^{6/7}` and `L^{6/7} ≥ 1`.
    have hsum : 2 + κ ≤ (2 + cvk ^ (-(6/7:ℝ))) * L ^ (6/7:ℝ) := by nlinarith
    have hB1 : 1 ≤ 2 * (Real.exp 4 * 5 * (2 + cvk ^ (-(6/7:ℝ)))) := by
      have he : 1 ≤ Real.exp 4 := Real.one_le_exp (by norm_num : (0:ℝ) ≤ 4)
      nlinarith
    -- absorb the `a^{-σ}` term using `B ≥ 1`
    have hstep1 : a ^ (-σ) ≤ (2 * (Real.exp 4 * 5 * (2 + cvk ^ (-(6/7:ℝ))))) * a ^ (-σ) := by
      simpa using mul_le_mul_of_nonneg_right hB1 hXnn
    -- absorb the `κ`-part on the `L^{6/7}` scale
    have hstep2 : 2 * (Real.exp 4 * 5 * (2 + κ)) ≤
        (2 * (Real.exp 4 * 5 * (2 + cvk ^ (-(6/7:ℝ))))) * L ^ (6/7:ℝ) := by
      have hcoefnn : 0 ≤ 2 * (Real.exp 4 * 5) := by positivity
      have h := mul_le_mul_of_nonneg_left hsum hcoefnn
      calc 2 * (Real.exp 4 * 5 * (2 + κ)) = (2 * (Real.exp 4 * 5)) * (2 + κ) := by ring
        _ ≤ (2 * (Real.exp 4 * 5)) * ((2 + cvk ^ (-(6/7:ℝ))) * L ^ (6/7:ℝ)) := h
        _ = (2 * (Real.exp 4 * 5 * (2 + cvk ^ (-(6/7:ℝ))))) * L ^ (6/7:ℝ) := by ring
    calc a ^ (-σ) + 2 * (Real.exp 4 * 5 * (2 + κ))
        ≤ (2 * (Real.exp 4 * 5 * (2 + cvk ^ (-(6/7:ℝ))))) * a ^ (-σ)
            + (2 * (Real.exp 4 * 5 * (2 + cvk ^ (-(6/7:ℝ))))) * L ^ (6/7:ℝ) :=
          add_le_add hstep1 hstep2
      _ = (2 * (Real.exp 4 * 5 * (2 + cvk ^ (-(6/7:ℝ))))) * (a ^ (-σ) + L ^ (6/7:ℝ)) := by ring

end Work.BMF
