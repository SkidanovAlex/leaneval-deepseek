import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Stability

/-- Auxiliary comparison: if `0 ≤ p ≤ 2`, `0 ≤ t` and `p * t ≤ 2`, then `p * t ^ α ≤ 2`
whenever `0 < α ≤ 1`.

Proof: if `t ≤ 1` then `t ^ α ≤ 1` and hence `p * t ^ α ≤ p ≤ 2`; if `1 ≤ t` then
`t ^ α ≤ t` (since `α ≤ 1` and `t ^ 1 = t`), so `p * t ^ α ≤ p * t ≤ 2`. -/
theorem mul_rpow_le_aux_of_mul_le {p t α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hp : 0 ≤ p) (ht : 0 ≤ t)
    (hB : p ≤ 2) (hpt : p * t ≤ 2) : p * t ^ α ≤ 2 := by
  rcases le_total t 1 with ht1 | ht1
  · have h1 : t ^ α ≤ 1 := Real.rpow_le_one ht ht1 hα.le
    calc p * t ^ α ≤ p * 1 := mul_le_mul_of_nonneg_left h1 hp
      _ = p := mul_one p
      _ ≤ 2 := hB
  · have h1 : t ^ α ≤ t := by
      calc t ^ α ≤ t ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le ht1 hα1
        _ = t := Real.rpow_one t
    calc p * t ^ α ≤ p * t := mul_le_mul_of_nonneg_left h1 hp
      _ ≤ 2 := hpt

theorem mul_rpow_le {p ρ d α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hρ : 0 ≤ ρ) (hd : 0 ≤ d)
    (hp : 0 ≤ p) (hA : p * ρ ≤ 2 * d) (hB : p ≤ 2) : p * ρ ^ α ≤ 2 * d ^ α := by
  rcases eq_or_lt_of_le hd with hd0 | hdpos
  · -- `d = 0`: the constraint `p * ρ ≤ 0` forces `p = 0` or `ρ = 0`, so both sides vanish
    subst hd0
    rw [Real.zero_rpow hα.ne', mul_zero]
    have hpρ : p * ρ = 0 := le_antisymm (by linarith [hA]) (mul_nonneg hp hρ)
    rcases mul_eq_zero.mp hpρ with h | h
    · simp [h]
    · simp [h, Real.zero_rpow hα.ne']
  · -- `d > 0`: set `t = ρ / d`, so that `p * t ≤ 2` and `ρ = t * d`
    set t : ℝ := ρ / d with htdef
    have ht : 0 ≤ t := div_nonneg hρ hdpos.le
    have htd : t * d = ρ := by rw [htdef]; exact div_mul_cancel₀ ρ hdpos.ne'
    have hpt : p * t ≤ 2 := by
      have h1 : p * t = p * ρ / d := by rw [htdef]; exact (mul_div_assoc p ρ d).symm
      rw [h1, div_le_iff₀ hdpos]
      linarith [hA]
    have hkey : p * t ^ α ≤ 2 :=
      mul_rpow_le_aux_of_mul_le hα hα1 hp ht hB hpt
    calc p * ρ ^ α = p * (t * d) ^ α := by rw [htd]
      _ = p * (t ^ α * d ^ α) := by rw [Real.mul_rpow ht hd]
      _ = (p * t ^ α) * d ^ α := by ring
      _ ≤ 2 * d ^ α := mul_le_mul_of_nonneg_right hkey (Real.rpow_nonneg hd α)

end Work.Stability
