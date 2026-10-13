import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Stability

theorem min_mul_le_max_mul_rpow {K M d : ℝ} {α : NNReal} (hK : 0 ≤ K) (hM : 0 ≤ M) (hd : 0 ≤ d) (hα : α ≤ 1) : min (K * d) (2 * M) ≤ max K (2 * M) * d ^ (α : ℝ) := by
  have hα0 : (0 : ℝ) ≤ (α : ℝ) := by positivity
  have hα1 : (α : ℝ) ≤ 1 := by exact_mod_cast hα
  have hmax : 0 ≤ max K (2 * M) := le_trans hK (le_max_left _ _)
  rcases eq_or_lt_of_le hd with hd0 | hdpos
  · -- d = 0
    rw [← hd0]
    have hnonneg : 0 ≤ max K (2 * M) * (0 : ℝ) ^ (α : ℝ) :=
      mul_nonneg (le_trans hK (le_max_left _ _)) (Real.rpow_nonneg (le_refl 0) _)
    calc min (K * 0) (2 * M) ≤ K * 0 := min_le_left _ _
      _ = 0 := by ring
      _ ≤ max K (2 * M) * (0 : ℝ) ^ (α : ℝ) := hnonneg
  · rcases lt_or_ge 1 d with hlt | hdle
    · -- 1 < d, use the `2 * M` branch
      have hd1 : 1 ≤ d := le_of_lt hlt
      have hpow : 1 ≤ d ^ (α : ℝ) := Real.one_le_rpow hd1 hα0
      calc min (K * d) (2 * M) ≤ 2 * M := min_le_right _ _
        _ = (2 * M) * 1 := by ring
        _ ≤ max K (2 * M) * d ^ (α : ℝ) :=
            mul_le_mul (le_max_right _ _) hpow (by norm_num) hmax
    · -- d ≤ 1, use the `K * d` branch and d ≤ d^α
      have hpow : d ≤ d ^ (α : ℝ) := by
        have h := Real.rpow_le_rpow_of_exponent_ge hdpos hdle hα1
        simpa using h
      have hpow0 : 0 ≤ d ^ (α : ℝ) := Real.rpow_nonneg hd _
      calc min (K * d) (2 * M) ≤ K * d := min_le_left _ _
        _ ≤ K * d ^ (α : ℝ) := mul_le_mul_of_nonneg_left hpow hK
        _ ≤ max K (2 * M) * d ^ (α : ℝ) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hpow0

end Work.Stability
