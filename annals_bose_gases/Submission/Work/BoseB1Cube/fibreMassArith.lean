import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube

theorem fibreMassArith {M : ℕ} (hM : 1 ≤ M) {δ' : ℝ} (hδ' : 0 < δ') (hδ'8 : δ' ≤ 1 / 8) :
    2 * (4 * δ') ^ (2 * M) * δ' ≤ (1 / 8) * (1 / 2) ^ M := by
  -- `4 δ' ≤ 1/2`, so `(4 δ') ^ (2 M) ≤ (1/2) ^ (2 M) = ((1/2) ^ M) ^ 2`.
  have h4δ' : 4 * δ' ≤ 1 / 2 := by linarith
  have h4δ'0 : (0 : ℝ) ≤ 4 * δ' := by linarith
  have hpow : (4 * δ') ^ (2 * M) ≤ (1 / 2) ^ (2 * M) :=
    pow_le_pow_left₀ h4δ'0 h4δ' _
  have h2M : (1 / 2 : ℝ) ^ (2 * M) = ((1 / 2) ^ M) ^ 2 := by
    rw [show 2 * M = M * 2 from by omega, pow_mul]
  -- `(1/2) ^ M ≤ 1/2` since `M ≥ 1` and `1/2 ∈ [0,1]`.
  have hc_le : (1 / 2 : ℝ) ^ M ≤ 1 / 2 := by
    have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 : ℝ) / 2 ≤ 1) hM
    simpa using this
  have hc0 : (0 : ℝ) ≤ (1 / 2) ^ M := pow_nonneg (by norm_num) _
  have hA : (4 * δ') ^ (2 * M) ≤ ((1 / 2) ^ M) ^ 2 := by
    calc (4 * δ') ^ (2 * M) ≤ (1 / 2) ^ (2 * M) := hpow
      _ = ((1 / 2) ^ M) ^ 2 := h2M
  -- With `c := (1/2)^M`: `2 · c² · δ' ≤ c²/4 ≤ c/8`, using `δ' ≤ 1/8` and `c ≤ 1/2`.
  nlinarith [hA, hc_le, hc0, hδ'8, hδ'.le]

end Work.BoseB1Cube
