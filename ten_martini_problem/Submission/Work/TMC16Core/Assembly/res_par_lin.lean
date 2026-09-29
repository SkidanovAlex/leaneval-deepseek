import Mathlib

namespace Work.TMC16Core.Assembly

theorem res_par_lin {L εf b : ℝ} {m : ℕ}
    (hL : 0 < L) (hεf0 : 0 < εf) (hεf : εf ≤ L / 1000)
    (hm : 1000 ≤ m) (hb0 : 0 ≤ b) (hb : b ≤ (m : ℝ) / 20 + 3) :
    (L + εf) * ((((2 * m - 1 : ℕ) : ℝ)) - 1 - ((((5 * m / 8 : ℕ) : ℝ)) - 1 - b))
      - ((((2 * m - 1 : ℕ) : ℝ)) + 1) * (23 * L / 32 + 2 * εf)
      + (L / 100) * ((((5 * m / 8 : ℕ) : ℝ)) - 1 - b) < 0 := by
  -- Abbreviate the two natural-number casts appearing in the statement.
  set N : ℝ := ((2 * m - 1 : ℕ) : ℝ) with hNdef
  set Q : ℝ := ((5 * m / 8 : ℕ) : ℝ) with hQdef
  have hmR : (1000 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  -- `N = 2m - 1` (the subtraction `2 * m - 1` is genuine because `m ≥ 1000`).
  have hN : N = 2 * (m : ℝ) - 1 := by
    rw [hNdef, Nat.cast_sub (show 1 ≤ 2 * m by omega)]
    push_cast
    ring
  -- Bounds for the integer division `Q = 5m / 8` : `Q ≤ 5m/8` and `Q ≥ (5m - 7)/8`.
  have hQ8nat : (5 * m / 8) * 8 ≤ 5 * m := Nat.div_mul_le_self _ _
  have hQ7nat : 5 * m ≤ (5 * m / 8) * 8 + 7 := by
    have h := Nat.div_add_mod (5 * m) 8
    have hmod : (5 * m) % 8 ≤ 7 := by
      have := Nat.mod_lt (5 * m) (by norm_num : 0 < 8)
      omega
    omega
  have hQ8 : Q * 8 ≤ 5 * (m : ℝ) := by rw [hQdef]; exact_mod_cast hQ8nat
  have hQ7 : 5 * (m : ℝ) ≤ Q * 8 + 7 := by rw [hQdef]; exact_mod_cast hQ7nat
  -- Both "coefficients" of the expanded expression are strictly negative.
  have hCe : N - 1 - (Q - 1 - b) - 2 * (N + 1) < 0 := by
    nlinarith [hN, hmR, hb, hQ8, hQ7]
  have hCL : N - 1 - (Q - 1 - b) - (N + 1) * (23 / 32) + (1 / 100) * (Q - 1 - b) < 0 := by
    nlinarith [hN, hmR, hb, hQ8, hQ7]
  -- Expand the whole left-hand side as `L * CL + εf * Ce`.
  have hexp : (L + εf) * (N - 1 - (Q - 1 - b))
      - (N + 1) * (23 * L / 32 + 2 * εf)
      + (L / 100) * (Q - 1 - b)
      = L * (N - 1 - (Q - 1 - b) - (N + 1) * (23 / 32) + (1 / 100) * (Q - 1 - b))
        + εf * (N - 1 - (Q - 1 - b) - 2 * (N + 1)) := by ring
  rw [hexp]
  have h1 : L * (N - 1 - (Q - 1 - b) - (N + 1) * (23 / 32) + (1 / 100) * (Q - 1 - b)) < 0 :=
    mul_neg_of_pos_of_neg hL hCL
  have h2 : εf * (N - 1 - (Q - 1 - b) - 2 * (N + 1)) < 0 :=
    mul_neg_of_pos_of_neg hεf0 hCe
  linarith

end Work.TMC16Core.Assembly
