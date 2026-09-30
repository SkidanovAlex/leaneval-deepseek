import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.vkN

/-- Basic facts about the short-interval scale `H = u ^ (-(1/k))` used in the
`v^k`-short-interval argument: `H ≥ 1`, the identity `H ^ (-(k-1)) = u * H`
(this is `H ^ (-(k-1)) = u ^ ((k-1)/k)`), and the smallness bound
`2 * H ^ (-(k-1)) ≤ 1` which is where the hypothesis `u ≤ 1/4` is used. -/
lemma rpow_theta_facts {k : ℕ} (hk : 3 ≤ k) {u H : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1 / 4)
    (hH : H = u ^ (-(1 / (k : ℝ)))) :
    1 ≤ H ∧ H ^ (-(((k - 1 : ℕ) : ℝ))) = u * H ∧ 2 * H ^ (-(((k - 1 : ℕ) : ℝ))) ≤ 1 := by
  have hk1 : 1 ≤ k := by omega
  have hk2 : 2 ≤ k := by omega
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkpos
  have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub hk1]; norm_num
  have hu_lt_one : u < 1 := by linarith
  have hu_le_one : u ≤ 1 := le_of_lt hu_lt_one
  have hu_nonneg : 0 ≤ u := le_of_lt hu0
  -- `H ≥ 1` since `u ≤ 1` and `-(1/k) ≤ 0`.
  have h1H : 1 ≤ H := by
    rw [hH, ← Real.rpow_zero u]
    exact Real.rpow_le_rpow_of_exponent_ge hu0 hu_le_one
      (neg_nonpos.mpr (by positivity))
  -- `H ^ (-(k-1)) = u ^ (-(1/k) * (-(k-1)))`
  have hpowH : H ^ (-(((k - 1 : ℕ) : ℝ))) = u ^ (-(1 / (k : ℝ)) * (-(((k - 1 : ℕ) : ℝ)))) := by
    rw [hH, ← Real.rpow_mul hu_nonneg]
  -- `u * H = u ^ (1 + -(1/k))`
  have hprod : u * H = u ^ (1 + -(1 / (k : ℝ))) := by
    rw [hH, Real.rpow_add hu0 1 (-(1 / (k : ℝ))), Real.rpow_one]
  -- the two exponents agree: `-(1/k) * (-(k-1)) = 1 - 1/k`
  have hexp : -(1 / (k : ℝ)) * (-(((k - 1 : ℕ) : ℝ))) = 1 + -(1 / (k : ℝ)) := by
    rw [hcast]
    field_simp
    ring
  -- exponent comparison: `u ^ (1 - 1/k) ≤ u ^ (1/2)` because `1/2 ≤ 1 - 1/k` and `u ≤ 1`
  have hle : u ^ (1 + -(1 / (k : ℝ))) ≤ u ^ (1 / 2 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_ge hu0 hu_le_one
    have hk2r : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    have hdiv : 1 / (k : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hk2r
    linarith
  -- and `u ^ (1/2) = sqrt u ≤ sqrt (1/4) = 1/2`
  have hsqrt : u ^ (1 / 2 : ℝ) ≤ 1 / 2 := by
    rw [← Real.sqrt_eq_rpow]
    calc Real.sqrt u ≤ Real.sqrt (1 / 4) := Real.sqrt_le_sqrt hu1
      _ = 1 / 2 := by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
        norm_num
  refine ⟨h1H, ?_, ?_⟩
  · rw [hpowH, hprod, hexp]
  · rw [hpowH, hexp]
    linarith

end Work.BMF.vkN
