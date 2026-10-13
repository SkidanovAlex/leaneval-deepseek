import Mathlib

namespace Work.WilE3.MPsi

set_option autoImplicit false

/-- The exponent bookkeeping of the descent step: from `c₁ ρ^Kexp ≤ m ≤ 2 Lip ρ`, `ρ ≤ 1`,
`Kexp + 1 ≤ κ`, `4^(κ+1) ρ < c₁`, `4 A' Lip² ρ ≤ 2`, `8 Lip² A' ρ ≤ 1` (`c₁ > 0`, `Lip ≥ 0`,
`A' > 0`) one gets `Lip A' m ≤ 1/2`, `A' m² + 2ρ ≤ 4ρ` and `2 (A' m² + 2ρ)^κ < m/2`. -/
theorem final_arith {m ρ c₁ Lip A' : ℝ} {Kexp κ : ℕ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hκ : Kexp + 1 ≤ κ)
    (hm : c₁ * ρ ^ Kexp ≤ m) (hm2 : m ≤ 2 * Lip * ρ)
    (hc1 : 0 < c₁) (hLip : 0 ≤ Lip) (hA' : 0 < A')
    (h1 : 4 ^ (κ + 1) * ρ < c₁) (h2 : 4 * A' * Lip ^ 2 * ρ ≤ 2)
    (h3 : 8 * Lip ^ 2 * A' * ρ ≤ 1) :
    Lip * A' * m ≤ 1 / 2 ∧ A' * m ^ 2 + 2 * ρ ≤ 4 * ρ ∧
      2 * (A' * m ^ 2 + 2 * ρ) ^ κ < m / 2 := by
  -- `m` is positive since it dominates `c₁ ρ^Kexp > 0`.
  have hm0 : 0 < m := lt_of_lt_of_le (mul_pos hc1 (pow_pos hρ Kexp)) hm
  -- (1) `Lip A' m ≤ 1/2`: bound `m ≤ 2 Lip ρ` and use `h3`.
  have hpart1 : Lip * A' * m ≤ 1 / 2 := by
    have h2' : Lip * A' * m ≤ Lip * A' * (2 * Lip * ρ) :=
      mul_le_mul_of_nonneg_left hm2 (mul_nonneg hLip (le_of_lt hA'))
    nlinarith [h2', h3]
  -- (2) `A' m² + 2ρ ≤ 4ρ`, i.e. `A' m² ≤ 2ρ`: square `m ≤ 2 Lip ρ` and use `h2`.
  have hpart2 : A' * m ^ 2 + 2 * ρ ≤ 4 * ρ := by
    have hmsq : m ^ 2 ≤ (2 * Lip * ρ) ^ 2 := pow_le_pow_left₀ (le_of_lt hm0) hm2 2
    have hA'm : A' * m ^ 2 ≤ A' * (2 * Lip * ρ) ^ 2 :=
      mul_le_mul_of_nonneg_left hmsq (le_of_lt hA')
    have h2ρ : 4 * A' * Lip ^ 2 * ρ * ρ ≤ 2 * ρ :=
      mul_le_mul_of_nonneg_right h2 (le_of_lt hρ)
    nlinarith [hA'm, h2ρ]
  -- The base `A' m² + 2ρ` is nonnegative, so we may raise the bound `(2)` to the `κ`-th power.
  have hbase0 : 0 ≤ A' * m ^ 2 + 2 * ρ := by nlinarith [hA', sq_nonneg m, hρ]
  have hpow : (A' * m ^ 2 + 2 * ρ) ^ κ ≤ (4 * ρ) ^ κ :=
    pow_le_pow_left₀ hbase0 hpart2 κ
  -- `ρ^κ ≤ ρ^(Kexp+1)` because `0 < ρ ≤ 1` and `Kexp + 1 ≤ κ`.
  have hρκ : ρ ^ κ ≤ ρ ^ (Kexp + 1) := pow_le_pow_of_le_one (le_of_lt hρ) hρ1 hκ
  have hstep : 4 ^ (κ + 1) * ρ ^ κ ≤ 4 ^ (κ + 1) * ρ ^ (Kexp + 1) :=
    mul_le_mul_of_nonneg_left hρκ (by positivity)
  -- `4^(κ+1) ρ < c₁` and `ρ^Kexp > 0` give `4^(κ+1) ρ^(Kexp+1) < c₁ ρ^Kexp`.
  have h1' : 4 ^ (κ + 1) * ρ * ρ ^ Kexp < c₁ * ρ ^ Kexp :=
    mul_lt_mul_of_pos_right h1 (pow_pos hρ Kexp)
  have hEq : (4 : ℝ) ^ (κ + 1) * ρ ^ (Kexp + 1) = 4 ^ (κ + 1) * ρ * ρ ^ Kexp := by
    rw [pow_succ]; ring
  have hlow : 4 ^ (κ + 1) * ρ ^ κ < c₁ * ρ ^ Kexp := by linarith
  -- Hence `4^(κ+1) ρ^κ < m`, i.e. `4 · 4^κ ρ^κ < m`.
  have hm_strict : 4 ^ (κ + 1) * ρ ^ κ < m := by linarith
  have hfour : (4 : ℝ) ^ (κ + 1) = 4 * 4 ^ κ := by rw [pow_succ]; ring
  have hm_strict' : 4 * 4 ^ κ * ρ ^ κ < m := by
    rw [hfour] at hm_strict; exact hm_strict
  -- (3) Combine: `2 (A' m² + 2ρ)^κ ≤ 2 (4ρ)^κ = 2 · 4^κ ρ^κ < m/2`.
  have hfinal : 2 * (A' * m ^ 2 + 2 * ρ) ^ κ < m / 2 := by
    have h1'' : 2 * (A' * m ^ 2 + 2 * ρ) ^ κ ≤ 2 * (4 * ρ) ^ κ := by linarith
    have h2'' : (4 * ρ) ^ κ = 4 ^ κ * ρ ^ κ := mul_pow 4 ρ κ
    linarith
  exact ⟨hpart1, hpart2, hfinal⟩

end Work.WilE3.MPsi
