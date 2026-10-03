import Mathlib

namespace Work.Pert.Pin

/-- Pure arithmetic core of the strip-gate estimate (version 4).

All the analytic content is pushed into the hypotheses: `L` is the log factor
`1 + log (2+M)`, `A ≥ L` is the full log expression `1 + log (2+M) + log (2+y)`,
and `G ≥ 1 + Ξ` is the geometric factor `1 + Ξ + 1/Ξ + 1/rr` (which is `≥ 3`).

The three ingredients are
* `(1 + 1/150 + 1/31) ≤ 2^44 G` (so the `Kp` slot absorbs its own `1/4 + s/4` part and the
  `y`-coefficient `s = 1/150 + 1/31` is harmless since `s ≤ 1/20`),
* `2^6 (1+Ξ) L + 2^11 ≤ 2^44 G A` (the `C₂` slot),
* `2^43 G A + O(1) ≤ 2^44 G A` (the constant slot). -/
private lemma arith_core_v4 {Ξ Kp C₂ L A G y : ℝ}
    (hKp : 0 ≤ Kp) (hC₂ : 0 ≤ C₂) (hy : 0 ≤ y)
    (hLnn : 0 ≤ L) (hLapp : L ≤ A) (hA1 : 1 ≤ A)
    (hG3 : 3 ≤ G) (hΞG : 1 + Ξ ≤ G) :
    Kp * L + 1 / 4
      + (C₂ * 2 ^ 6 * (1 + Ξ) * L + 2 ^ 43 * G * A)
      + (1 / 150 + 1 / 31) * (y + Kp * L + 1 / 4)
      + (2 * C₂ + 1 / 31) * 2 ^ 10
    ≤ (Kp + 1 + C₂) * 2 ^ 44 * G * A + y / 20 := by
  have hs : (1 : ℝ) / 150 + 1 / 31 ≤ 1 / 20 := by norm_num
  -- the `Kp` slot: `Kp * L * (1 + s) ≤ Kp * (2^44 G A)`
  have hAs : Kp * L + (1 / 150 + 1 / 31) * (Kp * L) ≤ Kp * (2 ^ 44 * G * A) := by
    have h1 : Kp * L ≤ Kp * A := mul_le_mul_of_nonneg_left hLapp hKp
    have h2 : (1 : ℝ) + (1 / 150 + 1 / 31) ≤ 2 ^ 44 * G := by nlinarith [hG3]
    have h3 : Kp * L * (1 + (1 / 150 + 1 / 31)) ≤ Kp * A * (2 ^ 44 * G) :=
      calc Kp * L * (1 + (1 / 150 + 1 / 31)) ≤ Kp * A * (1 + (1 / 150 + 1 / 31)) :=
            mul_le_mul_of_nonneg_right h1 (by linarith)
        _ ≤ Kp * A * (2 ^ 44 * G) :=
            mul_le_mul_of_nonneg_left h2 (mul_nonneg hKp (by linarith))
    have h4 : Kp * A * (2 ^ 44 * G) = Kp * (2 ^ 44 * G * A) := by ring
    linarith [h3, h4]
  have hGA : (3 : ℝ) ≤ G * A := by
    have h := mul_le_mul hG3 hA1 (by norm_num : (0 : ℝ) ≤ 1) (by linarith)
    linarith
  -- the `C₂` slot
  have hBs : C₂ * 2 ^ 6 * (1 + Ξ) * L + 2048 * C₂ ≤ C₂ * (2 ^ 44 * G * A) := by
    have h1a : (1 + Ξ) * L ≤ G * A := by
      have hL : (1 + Ξ) * L ≤ G * L := mul_le_mul_of_nonneg_right hΞG hLnn
      have hA' : G * L ≤ G * A := mul_le_mul_of_nonneg_left hLapp (by linarith)
      linarith
    have h1b : (2048 : ℝ) ≤ 2 ^ 43 * G * A := by nlinarith [hGA]
    have h1 : 2 ^ 6 * (1 + Ξ) * L + 2048 ≤ 2 ^ 44 * G * A := by nlinarith [h1a, h1b]
    have h2 : C₂ * (2 ^ 6 * (1 + Ξ) * L + 2048) ≤ C₂ * (2 ^ 44 * G * A) :=
      mul_le_mul_of_nonneg_left h1 hC₂
    linarith [h2]
  -- the constant slot
  have hCs :
      2 ^ 43 * G * A + 1 / 4 + (1 / 150 + 1 / 31) * (1 / 4) + 1024 / 31
        ≤ 2 ^ 44 * G * A := by
    have hq : 1 / 4 + (1 / 150 + 1 / 31) * (1 / 4) + 1024 / 31 ≤ 2 ^ 43 * G * A := by
      nlinarith [hGA]
    nlinarith [hq]
  have hDs : (1 / 150 + 1 / 31) * y ≤ y / 20 := by
    have h := mul_le_mul_of_nonneg_right hs hy
    linarith
  nlinarith [hAs, hBs, hCs, hDs]

theorem arith_strip_v4 {Ξ rr M Kp C₂ y : ℝ}
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M) (hKp : 0 ≤ Kp) (hC₂ : 0 ≤ C₂) (hy : 0 ≤ y) :
    Kp * (1 + Real.log (2 + M)) + 1 / 4
      + (C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
          + 2 ^ 43 * (1 + Ξ + 1 / Ξ + 1 / rr)
              * (1 + Real.log (2 + M) + Real.log (2 + y)))
      + (1 / 150 + 1 / 31) * (y + Kp * (1 + Real.log (2 + M)) + 1 / 4)
      + (2 * C₂ + 1 / 31) * 2 ^ 10
    ≤ (Kp + 1 + C₂) * 2 ^ 44 * (1 + Ξ + 1 / Ξ + 1 / rr)
        * (1 + Real.log (2 + M) + Real.log (2 + y)) + y / 20 := by
  have hM1024 : (1024 : ℝ) ≤ M := by norm_num at hM; exact hM
  have hlogM : 0 ≤ Real.log (2 + M) := Real.log_nonneg (by linarith)
  have hlogy : 0 ≤ Real.log (2 + y) := Real.log_nonneg (by linarith)
  have hinvΞ : 0 < 1 / Ξ := one_div_pos.mpr hΞ
  have hinvrr : 0 < 1 / rr := one_div_pos.mpr hrr
  have hself : 2 ≤ Ξ + 1 / Ξ := by
    have hsq : 0 ≤ (Ξ - 1) ^ 2 / Ξ := div_nonneg (sq_nonneg _) (le_of_lt hΞ)
    have h : Ξ + 1 / Ξ - 2 = (Ξ - 1) ^ 2 / Ξ := by field_simp; ring
    linarith
  exact arith_core_v4 (Ξ := Ξ) (Kp := Kp) (C₂ := C₂)
    (L := 1 + Real.log (2 + M))
    (A := 1 + Real.log (2 + M) + Real.log (2 + y))
    (G := 1 + Ξ + 1 / Ξ + 1 / rr) (y := y)
    hKp hC₂ hy (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)

end Work.Pert.Pin
