import Mathlib

namespace Work.Main.param

/-- Polynomial-vs-exponential auxiliary inequality: for `s ≥ 16`, the quadratic
`6 (s+1)^2 + 1` is dominated by `2 ^ (2 s)`.  Proved by induction from `s = 16`,
where each increment more than doubles the right-hand side. -/
lemma six_sq_add_one_le_two_pow : ∀ s : ℕ, 16 ≤ s → 6 * (s + 1) ^ 2 + 1 ≤ 2 ^ (2 * s) := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      have hA : 6 * ((k + 1) + 1) ^ 2 + 1 ≤ 4 * (6 * (k + 1) ^ 2 + 1) := by nlinarith
      have hB : 4 * (6 * (k + 1) ^ 2 + 1) ≤ 4 * 2 ^ (2 * k) := Nat.mul_le_mul_left 4 ih
      have hC : 4 * 2 ^ (2 * k) = 2 ^ (2 * (k + 1)) := by
        rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]
        ring
      calc 6 * ((k + 1) + 1) ^ 2 + 1 ≤ 4 * (6 * (k + 1) ^ 2 + 1) := hA
        _ ≤ 4 * 2 ^ (2 * k) := hB
        _ = 2 ^ (2 * (k + 1)) := hC

/-- For `b ≥ 256`, `6 b + 1` is bounded by `2 ^ (2 √b)`; combined with
`(16 K)^2 ≤ b` (i.e. `16 K ≤ √b`) this gives the two-dimensional bound. -/
lemma six_mul_add_one_le_sqrt_pow {b : ℕ} (hb : 256 ≤ b) :
    6 * b + 1 ≤ 2 ^ (2 * Nat.sqrt b) := by
  have hs : 16 ≤ Nat.sqrt b := by
    have h1 : (256 : ℕ).sqrt ≤ b.sqrt := Nat.sqrt_le_sqrt hb
    have h2 : (256 : ℕ).sqrt = 16 := by norm_num
    omega
  have hb2 : b + 1 ≤ (Nat.sqrt b + 1) ^ 2 := by
    have h := Nat.lt_succ_sqrt' b
    rw [Nat.succ_eq_add_one] at h
    exact Nat.lt_iff_add_one_le.mp h
  have hle : 6 * b + 1 ≤ 6 * (Nat.sqrt b + 1) ^ 2 + 1 := by nlinarith
  exact le_trans hle (six_sq_add_one_le_two_pow _ hs)

/-- Core estimate: for `b ≥ 256` and `256 K^2 ≤ b` one has `(6 b + 1)^K ≤ 2^(b/8)`.
Writing `s = √b`: `16K ≤ s`, `6b+1 ≤ 2^(2s)`, hence `(6b+1)^K ≤ 2^(2sK) ≤ 2^(s²/8) ≤ 2^(b/8)`. -/
lemma base_pow_le {b K : ℕ} (hb : 256 ≤ b) (hK : 256 * K ^ 2 ≤ b) :
    (6 * b + 1) ^ K ≤ 2 ^ (b / 8) := by
  have hsq : (16 * K) ^ 2 ≤ b := by
    calc (16 * K) ^ 2 = 256 * K ^ 2 := by ring
      _ ≤ b := hK
  have h16K : 16 * K ≤ Nat.sqrt b := Nat.le_sqrt'.mpr hsq
  have hsix : 6 * b + 1 ≤ 2 ^ (2 * Nat.sqrt b) := six_mul_add_one_le_sqrt_pow hb
  have h2sK : 2 * Nat.sqrt b * K ≤ Nat.sqrt b ^ 2 / 8 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 8)]
    calc 2 * Nat.sqrt b * K * 8 = 16 * K * Nat.sqrt b := by ring
      _ ≤ Nat.sqrt b * Nat.sqrt b := Nat.mul_le_mul_right _ h16K
      _ = Nat.sqrt b ^ 2 := by ring
  calc (6 * b + 1) ^ K ≤ (2 ^ (2 * Nat.sqrt b)) ^ K := Nat.pow_le_pow_left hsix K
    _ = 2 ^ (2 * Nat.sqrt b * K) := (pow_mul 2 (2 * Nat.sqrt b) K).symm
    _ ≤ 2 ^ (Nat.sqrt b ^ 2 / 8) := Nat.pow_le_pow_right (by norm_num) h2sK
    _ ≤ 2 ^ (b / 8) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.div_le_div_right (Nat.sqrt_le' b))

theorem pow_six_mul_add_one {b K : ℕ} (hb : 256 ≤ b) (hK : 256 * K ^ 2 ≤ b) :
    (6 * b + 1) ^ (K * 1729) ≤ 2 ^ (1729 * b / 8) := by
  have hbase := base_pow_le hb hK
  calc (6 * b + 1) ^ (K * 1729) = ((6 * b + 1) ^ K) ^ 1729 := pow_mul (6 * b + 1) K 1729
    _ ≤ (2 ^ (b / 8)) ^ 1729 := Nat.pow_le_pow_left hbase 1729
    _ = 2 ^ ((b / 8) * 1729) := (pow_mul 2 (b / 8) 1729).symm
    _ ≤ 2 ^ (1729 * b / 8) := by
        apply Nat.pow_le_pow_right (by norm_num)
        rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 8)]
        calc (b / 8) * 1729 * 8 = 1729 * (b / 8 * 8) := by ring
          _ ≤ 1729 * b := Nat.mul_le_mul_left 1729 (Nat.div_mul_le_self b 8)

end Work.Main.param
