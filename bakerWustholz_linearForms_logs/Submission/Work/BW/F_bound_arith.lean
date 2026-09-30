import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Arithmetic core of the "F" bound in the Baker--Wüstholz proof: for `d ≥ 1` and any `m`,
`m · d · (9(m-1)d^3)^{m-1} ≤ (9 m d^3)^m`. -/
theorem F_bound_arith (m : ℕ) {d : ℝ} (hd : 1 ≤ d) :
    (m : ℝ) * d * (9 * ((m : ℝ) - 1) * d ^ 3) ^ (m - 1) ≤ (9 * (m : ℝ) * d ^ 3) ^ m := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    norm_num
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    have hd0 : (0 : ℝ) ≤ d := by linarith
    have hcast : (((n + 1 : ℕ) : ℝ) - 1) = (n : ℝ) := by push_cast; ring
    have hsub : (n + 1) - 1 = n := by omega
    rw [hcast, hsub]
    -- `9 n d^3 ≤ 9 (n+1) d^3`, so the `n`-th powers are comparable
    have hA0 : (0 : ℝ) ≤ 9 * (n : ℝ) * d ^ 3 := by positivity
    have hAB : 9 * (n : ℝ) * d ^ 3 ≤ 9 * ((n + 1 : ℕ) : ℝ) * d ^ 3 := by
      have h1 : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
      nlinarith [mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 9 * d ^ 3 by positivity)]
    have step1 : (9 * (n : ℝ) * d ^ 3) ^ n ≤ (9 * ((n + 1 : ℕ) : ℝ) * d ^ 3) ^ n :=
      pow_le_pow_left₀ hA0 hAB n
    have hnd : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) * d := by positivity
    have step2 : ((n + 1 : ℕ) : ℝ) * d * (9 * (n : ℝ) * d ^ 3) ^ n ≤
                 ((n + 1 : ℕ) : ℝ) * d * (9 * ((n + 1 : ℕ) : ℝ) * d ^ 3) ^ n :=
      mul_le_mul_of_nonneg_left step1 hnd
    -- the remaining factor: `d ≤ 9 d^3`
    have hd_le : d ≤ 9 * d ^ 3 := by
      have h1 : (1 : ℝ) ≤ d ^ 2 := by nlinarith [sq_nonneg (d - 1)]
      have h2 : d * 1 ≤ d * d ^ 2 := mul_le_mul_of_nonneg_left h1 hd0
      nlinarith [h2]
    have hle : ((n + 1 : ℕ) : ℝ) * d ≤ 9 * ((n + 1 : ℕ) : ℝ) * d ^ 3 := by
      have h2 : ((n + 1 : ℕ) : ℝ) * d ≤ ((n + 1 : ℕ) : ℝ) * (9 * d ^ 3) :=
        mul_le_mul_of_nonneg_left hd_le (by positivity)
      linarith [h2]
    have hBpow : (0 : ℝ) ≤ (9 * ((n + 1 : ℕ) : ℝ) * d ^ 3) ^ n := by positivity
    have step3 : ((n + 1 : ℕ) : ℝ) * d * (9 * ((n + 1 : ℕ) : ℝ) * d ^ 3) ^ n ≤
                 (9 * ((n + 1 : ℕ) : ℝ) * d ^ 3) ^ (n + 1) := by
      have h3 := mul_le_mul_of_nonneg_right hle hBpow
      have hp : (9 * ((n + 1 : ℕ) : ℝ) * d ^ 3) ^ (n + 1)
          = 9 * ((n + 1 : ℕ) : ℝ) * d ^ 3 * (9 * ((n + 1 : ℕ) : ℝ) * d ^ 3) ^ n :=
        pow_succ' _ n
      rw [hp]
      exact h3
    exact le_trans step2 step3

end Work.BW
