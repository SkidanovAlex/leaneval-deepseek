import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Cyl.DecayAux

theorem rhoP_sq_mul_cos_rpow_div_le {q ρ r : ℝ} (hq : 1 ≤ q) (hr : 0 < r) (hrρ : r ≤ ρ) :
    ρ ^ 2 * (r / ρ) ^ q / r ≤ ρ := by
  have hρ : 0 < ρ := lt_of_lt_of_le hr hrρ
  have hρne : ρ ≠ 0 := ne_of_gt hρ
  have ht0 : 0 ≤ r / ρ := le_of_lt (div_pos hr hρ)
  have ht1 : r / ρ ≤ 1 := (div_le_one hρ).mpr hrρ
  -- a base in `[0,1]` raised to an exponent `≥ 1` is dominated by the base
  have hT : (r / ρ) ^ q ≤ r / ρ := Real.rpow_le_self_of_le_one ht0 ht1 hq
  have hmain : ρ ^ 2 * (r / ρ) ^ q ≤ ρ * r := by
    calc ρ ^ 2 * (r / ρ) ^ q = ρ * (ρ * (r / ρ) ^ q) := by ring
      _ ≤ ρ * (ρ * (r / ρ)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hT (le_of_lt hρ)) (le_of_lt hρ)
      _ = ρ * r := by rw [mul_div_cancel₀ r hρne]
  rw [div_le_iff₀ hr]
  exact hmain

end Work.FTS.BSIdent.Cyl.DecayAux
