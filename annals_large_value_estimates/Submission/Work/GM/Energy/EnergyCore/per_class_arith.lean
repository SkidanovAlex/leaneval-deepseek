import Mathlib

namespace Work.GM.Energy.EnergyCore

theorem per_class_arith {ε : ℝ} {b u s Wc E T K Cloc Chb Cw mm MM : ℝ}
    (hb : 0 ≤ b) (hu : 0 ≤ u) (hs : 0 ≤ s) (hWc : 0 ≤ Wc) (hE : 0 ≤ E) (hMM : 0 ≤ MM)
    (hK : 0 < K) (hCloc : 0 ≤ Cloc) (hChb : 0 ≤ Chb) (hCw : 0 ≤ Cw)
    (hpow : 0 ≤ (2 * (T + 1)) ^ (ε / 2)) (hpow2 : 0 ≤ (2 * (T + 1)) ^ ((1 : ℝ) / 2))
    (hb1 : b ^ 2 * u ^ 2 ≤ Wc ^ 4) (hb2 : b ^ 2 * u ≤ E)
    (hb3 : b ^ 2 * u ^ ((5 : ℝ) / 4) ≤ E ^ ((3 : ℝ) / 4) * Wc)
    (hb4 : b ^ 2 * u ^ 2 ≤ E * Wc ^ 2)
    (hS : s ≤ K * Chb * (2 * (T + 1)) ^ (ε / 2) *
        (u ^ 2 * MM + u * MM ^ 2 + (2 * (T + 1)) ^ ((1 : ℝ) / 2) * u ^ ((5 : ℝ) / 4) * MM)) :
    (2 * b) ^ 2 * (4 * K * Cloc ^ 2 * s + 2 * (Cw / K ^ mm * (MM + 1)) ^ 2 * u ^ 2)
      ≤ 16 * K ^ 2 * Cloc ^ 2 * Chb * (2 * (T + 1)) ^ (ε / 2) *
            (Wc ^ 4 * MM + E * MM ^ 2 + (2 * (T + 1)) ^ ((1 : ℝ) / 2) * E ^ ((3 : ℝ) / 4) * Wc * MM)
        + 8 * (Cw / K ^ mm * (MM + 1)) ^ 2 * E * Wc ^ 2 := by
  set a : ℝ := (2 * (T + 1)) ^ (ε / 2) with ha
  set q : ℝ := (2 * (T + 1)) ^ ((1 : ℝ) / 2) with hq
  set z : ℝ := (Cw / K ^ mm * (MM + 1)) ^ 2 with hz
  have ha0 : 0 ≤ a := by rw [ha]; exact hpow
  have hq0 : 0 ≤ q := by rw [hq]; exact hpow2
  have hz0 : 0 ≤ z := by rw [hz]; exact sq_nonneg _
  have hK0 : 0 ≤ K := le_of_lt hK
  have hb0 : 0 ≤ b ^ 2 := sq_nonneg b
  -- bound each of the three terms of the S-sum
  have t1 : b ^ 2 * u ^ 2 * MM ≤ Wc ^ 4 * MM := mul_le_mul_of_nonneg_right hb1 hMM
  have t2 : b ^ 2 * u * MM ^ 2 ≤ E * MM ^ 2 := mul_le_mul_of_nonneg_right hb2 (sq_nonneg MM)
  have t3 : q * (b ^ 2 * u ^ ((5 : ℝ) / 4) * MM) ≤ q * (E ^ ((3 : ℝ) / 4) * Wc * MM) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb3 hMM) hq0
  have key : b ^ 2 * (u ^ 2 * MM + u * MM ^ 2 + q * u ^ ((5 : ℝ) / 4) * MM)
      ≤ Wc ^ 4 * MM + E * MM ^ 2 + q * (E ^ ((3 : ℝ) / 4) * Wc * MM) := by
    have e : b ^ 2 * (u ^ 2 * MM + u * MM ^ 2 + q * u ^ ((5 : ℝ) / 4) * MM)
        = b ^ 2 * u ^ 2 * MM + b ^ 2 * u * MM ^ 2
          + q * (b ^ 2 * u ^ ((5 : ℝ) / 4) * MM) := by ring
    rw [e]; linarith [t1, t2, t3]
  have hKChba : 0 ≤ K * Chb * a := mul_nonneg (mul_nonneg hK0 hChb) ha0
  have keyS : b ^ 2 * s ≤ K * Chb * a * (Wc ^ 4 * MM + E * MM ^ 2 + q * (E ^ ((3 : ℝ) / 4) * Wc * MM)) := by
    calc b ^ 2 * s
        ≤ b ^ 2 * (K * Chb * a * (u ^ 2 * MM + u * MM ^ 2 + q * u ^ ((5 : ℝ) / 4) * MM)) :=
          mul_le_mul_of_nonneg_left hS hb0
      _ = K * Chb * a * (b ^ 2 * (u ^ 2 * MM + u * MM ^ 2 + q * u ^ ((5 : ℝ) / 4) * MM)) := by ring
      _ ≤ K * Chb * a * (Wc ^ 4 * MM + E * MM ^ 2 + q * (E ^ ((3 : ℝ) / 4) * Wc * MM)) :=
          mul_le_mul_of_nonneg_left key hKChba
  have keyA : 16 * K * Cloc ^ 2 * (b ^ 2 * s)
      ≤ 16 * K ^ 2 * Cloc ^ 2 * Chb * a
          * (Wc ^ 4 * MM + E * MM ^ 2 + q * (E ^ ((3 : ℝ) / 4) * Wc * MM)) := by
    calc 16 * K * Cloc ^ 2 * (b ^ 2 * s)
        ≤ 16 * K * Cloc ^ 2
            * (K * Chb * a * (Wc ^ 4 * MM + E * MM ^ 2 + q * (E ^ ((3 : ℝ) / 4) * Wc * MM))) :=
          mul_le_mul_of_nonneg_left keyS (by positivity)
      _ = 16 * K ^ 2 * Cloc ^ 2 * Chb * a
            * (Wc ^ 4 * MM + E * MM ^ 2 + q * (E ^ ((3 : ℝ) / 4) * Wc * MM)) := by ring
  have keyB : 8 * z * (b ^ 2 * u ^ 2) ≤ 8 * z * (E * Wc ^ 2) :=
    mul_le_mul_of_nonneg_left hb4 (by positivity)
  have expand : (2 * b) ^ 2 * (4 * K * Cloc ^ 2 * s + 2 * z * u ^ 2)
      = 16 * K * Cloc ^ 2 * (b ^ 2 * s) + 8 * z * (b ^ 2 * u ^ 2) := by ring
  rw [expand]
  linarith [keyA, keyB]

end Work.GM.Energy.EnergyCore
