import Mathlib

namespace Work.OddCurve.LowSlope

/-- Elementary arithmetic core: for `a ≥ 4` and `b = a - 1`,
`(b + (5/4) a)^2 ≤ (2/3) · a b^2 · (27/8)`. -/
private lemma sdC_arith {a b : ℝ} (hb : b = a - 1) (ha : 4 ≤ a) :
    (b + a * (5 / 4)) ^ 2 ≤ (2 / 3) * (a * b ^ 2 * (27 / 8)) := by
  subst hb
  have key : 36 * a * (a - 1) ^ 2 - (9 * a - 4) ^ 2
      = (a - 4) * (36 * a ^ 2 - 9 * a + 72) + 272 := by ring
  have h1 : 0 ≤ (a - 4) * (36 * a ^ 2 - 9 * a + 72) := by
    apply mul_nonneg (by linarith)
    nlinarith [sq_nonneg (4 * a - 1)]
  nlinarith [key, h1]

/-- From `3/8 ≤ R^(2n+2)` (with `n ≥ 1`) deduce `3/4 ≤ R`. -/
private lemma sdC_pow_lower {n : ℕ} (hn : 1 ≤ n) {R : ℝ} (hR : 0 < R)
    (h1 : 3 / 8 ≤ R ^ (2 * n + 2)) : 3 / 4 ≤ R := by
  have hn2 : (4 : ℕ) ≤ 2 * n + 2 := by omega
  have hle : (3 / 4 : ℝ) ^ (2 * n + 2) ≤ (3 / 4 : ℝ) ^ 4 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hn2
  have h4 : (3 / 4 : ℝ) ^ 4 = 81 / 256 := by norm_num
  have hbase : (3 / 4 : ℝ) ^ (2 * n + 2) ≤ 3 / 8 := by linarith
  have hpow : (3 / 4 : ℝ) ^ (2 * n + 2) ≤ R ^ (2 * n + 2) := le_trans hbase h1
  exact (pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 4) hR.le
    (by omega : 2 * n + 2 ≠ 0)).mp hpow

/-- From `R^(2n+2) ≤ 15/8` (with `n ≥ 1`) deduce `R ≤ 5/4`. -/
private lemma sdC_pow_upper {n : ℕ} (hn : 1 ≤ n) {R : ℝ} (hR : 0 < R)
    (h2 : R ^ (2 * n + 2) ≤ 15 / 8) : R ≤ 5 / 4 := by
  have hn2 : (4 : ℕ) ≤ 2 * n + 2 := by omega
  have hle : (5 / 4 : ℝ) ^ 4 ≤ (5 / 4 : ℝ) ^ (2 * n + 2) :=
    pow_le_pow_right₀ (by norm_num) hn2
  have h4 : (5 / 4 : ℝ) ^ 4 = 625 / 256 := by norm_num
  have hbase : (15 / 8 : ℝ) ≤ (5 / 4 : ℝ) ^ (2 * n + 2) := by linarith
  have hpow : R ^ (2 * n + 2) ≤ (5 / 4 : ℝ) ^ (2 * n + 2) := le_trans h2 hbase
  exact (pow_le_pow_iff_left₀ hR.le (by norm_num : (0 : ℝ) ≤ 5 / 4)
    (by omega : 2 * n + 2 ≠ 0)).mp hpow

theorem second_deriv_C_le (n : ℕ) (hn : 1 ≤ n) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (ha1 : 3 / 8 ≤ R ^ (2 * n + 2)) (ha2 : R ^ (2 * n + 2) ≤ 15 / 8)
    (hb1 : 3 / 8 ≤ r ^ (2 * n + 2)) (hb2 : r ^ (2 * n + 2) ≤ 15 / 8)
    (hm : |R ^ (2 * n + 2) + r ^ (2 * n + 2) - 2| ≤ 1 / 2)
    (hv : |R ^ (2 * n + 1) - r ^ (2 * n + 1)| ≤ 1 / 2) :
    let k1 : ℝ := ((2 * n + 1 : ℕ) : ℝ)
    let k2 : ℝ := ((2 * n + 2 : ℕ) : ℝ)
    let p : ℝ := 1 - 2 * |R ^ (2 * n + 2) + r ^ (2 * n + 2) - 2|
    let q : ℝ := 1 - 2 * |R ^ (2 * n + 1) - r ^ (2 * n + 1)|
    (k1 + k2 * R) * (k1 * p + k2 * R * q) / (k2 * k1 ^ 2 * (R * r) ^ (2 * n) * (R + r) ^ 3) ≤ 2 / 3 := by
  dsimp only
  have hn2 : (4 : ℕ) ≤ 2 * n + 2 := by omega
  set a : ℝ := ((2 * n + 2 : ℕ) : ℝ) with ha
  set b : ℝ := ((2 * n + 1 : ℕ) : ℝ) with hb
  have hba : b = a - 1 := by rw [ha, hb]; push_cast; ring
  have ha4 : 4 ≤ a := by rw [ha]; exact_mod_cast hn2
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by rw [hba]; linarith
  have hR3 : 3 / 4 ≤ R := sdC_pow_lower hn hR ha1
  have hr3 : 3 / 4 ≤ r := sdC_pow_lower hn hr hb1
  have hR5 : R ≤ 5 / 4 := sdC_pow_upper hn hR ha2
  -- bound the numerator
  have hnum : (b + a * R) * (b * (1 - 2 * |R ^ (2 * n + 2) + r ^ (2 * n + 2) - 2|)
        + a * R * (1 - 2 * |R ^ (2 * n + 1) - r ^ (2 * n + 1)|)) ≤ (b + a * (5 / 4)) ^ 2 := by
    have hp : 1 - 2 * |R ^ (2 * n + 2) + r ^ (2 * n + 2) - 2| ≤ 1 := by
      have h := abs_nonneg (R ^ (2 * n + 2) + r ^ (2 * n + 2) - 2); linarith
    have hq : 1 - 2 * |R ^ (2 * n + 1) - r ^ (2 * n + 1)| ≤ 1 := by
      have h := abs_nonneg (R ^ (2 * n + 1) - r ^ (2 * n + 1)); linarith
    have hbR : (0 : ℝ) ≤ a * R := by positivity
    have h1 : b * (1 - 2 * |R ^ (2 * n + 2) + r ^ (2 * n + 2) - 2|)
        + a * R * (1 - 2 * |R ^ (2 * n + 1) - r ^ (2 * n + 1)|) ≤ b + a * R := by
      have h1' := mul_le_mul_of_nonneg_left hp hb0.le
      have h2' := mul_le_mul_of_nonneg_left hq hbR
      linarith
    have h2 : b + a * R ≤ b + a * (5 / 4) := by
      have h := mul_le_mul_of_nonneg_left hR5 ha0.le
      linarith
    calc (b + a * R) * (b * (1 - 2 * |R ^ (2 * n + 2) + r ^ (2 * n + 2) - 2|)
            + a * R * (1 - 2 * |R ^ (2 * n + 1) - r ^ (2 * n + 1)|))
        ≤ (b + a * R) * (b + a * R) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (b + a * R) ^ 2 := by ring
      _ ≤ (b + a * (5 / 4)) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
  -- the product `R^(2n+2) · r^(2n+2)` is at least `27/64`
  have ht : 27 / 64 ≤ (R * r) ^ (2 * n + 2) := by
    rw [mul_pow]
    have hu0 : (0 : ℝ) ≤ R ^ (2 * n + 2) := pow_nonneg hR.le _
    have huv : 3 / 2 ≤ R ^ (2 * n + 2) + r ^ (2 * n + 2) := by
      have h := (abs_le.mp hm).1; linarith
    rcases le_total (R ^ (2 * n + 2)) (9 / 8) with h | h
    · have hvv : 3 / 2 - R ^ (2 * n + 2) ≤ r ^ (2 * n + 2) := by linarith
      have hmul := mul_le_mul_of_nonneg_left hvv hu0
      have hquad : 0 ≤ (R ^ (2 * n + 2) - 3 / 8) * (9 / 8 - R ^ (2 * n + 2)) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith [hmul, hquad]
    · have hmul := mul_le_mul_of_nonneg_left hb1 hu0
      nlinarith [hmul, h]
  -- hence `(R r)^(2n) · (R + r)^3 ≥ 27/8`
  have hE : 27 / 8 ≤ (R * r) ^ (2 * n) * (R + r) ^ 3 := by
    have hsum : 3 / 2 ≤ R + r := by linarith
    have ht0 : 0 < R * r := mul_pos hR hr
    have ht0' : (0 : ℝ) ≤ R * r := ht0.le
    rcases le_total (R * r) 1 with hle | hge
    · have hs0 : 0 ≤ Real.sqrt (R * r) := Real.sqrt_nonneg _
      have hsle : Real.sqrt (R * r) ≤ 1 := by
        rw [Real.sqrt_le_left (by norm_num)]; simpa using hle
      have h2 : 2 * Real.sqrt (R * r) ≤ R + r := by
        have hsq : Real.sqrt (R * r) ≤ (R + r) / 2 := by
          rw [Real.sqrt_le_left (by positivity)]
          nlinarith [sq_nonneg (R - r)]
        linarith
      have h3 : (2 * Real.sqrt (R * r)) ^ 3 ≤ (R + r) ^ 3 :=
        pow_le_pow_left₀ (by positivity) h2 3
      have hs34 : (Real.sqrt (R * r)) ^ 4 ≤ (Real.sqrt (R * r)) ^ 3 :=
        pow_le_pow_of_le_one hs0 hsle (by norm_num)
      have hs4 : (Real.sqrt (R * r)) ^ 4 = (R * r) ^ 2 := by
        rw [show (Real.sqrt (R * r)) ^ 4 = ((Real.sqrt (R * r)) ^ 2) ^ 2 by ring,
          Real.sq_sqrt ht0']
      have hcube : 8 * (R * r) ^ 2 ≤ (R + r) ^ 3 := by
        have hthis : (2 * Real.sqrt (R * r)) ^ 3 = 8 * (Real.sqrt (R * r)) ^ 3 := by ring
        nlinarith [h3, hs34, hs4, hthis]
      have hmain : 8 * (R * r) ^ (2 * n + 2) ≤ (R * r) ^ (2 * n) * (R + r) ^ 3 := by
        have heq : (R * r) ^ (2 * n) * (8 * (R * r) ^ 2) = 8 * (R * r) ^ (2 * n + 2) := by
          rw [pow_add]; ring
        rw [← heq]
        exact mul_le_mul_of_nonneg_left hcube (pow_nonneg ht0' _)
      linarith [ht, hmain]
    · have h1 : 1 ≤ (R * r) ^ (2 * n) := one_le_pow₀ hge
      have h3 : (3 / 2 : ℝ) ^ 3 ≤ (R + r) ^ 3 := pow_le_pow_left₀ (by norm_num) hsum 3
      nlinarith [h1, h3, ht0', pow_nonneg ht0' (2 * n)]
  -- final assembly
  have harith : (b + a * (5 / 4)) ^ 2 ≤ (2 / 3) * (a * b ^ 2 * (27 / 8)) := sdC_arith hba ha4
  have hD : a * b ^ 2 * (27 / 8) ≤ a * b ^ 2 * (R * r) ^ (2 * n) * (R + r) ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hE (by positivity : (0 : ℝ) ≤ a * b ^ 2)
    have heq : a * b ^ 2 * ((R * r) ^ (2 * n) * (R + r) ^ 3)
        = a * b ^ 2 * (R * r) ^ (2 * n) * (R + r) ^ 3 := by ring
    linarith [h, heq]
  have hDpos : 0 < a * b ^ 2 * (R * r) ^ (2 * n) * (R + r) ^ 3 := by positivity
  rw [div_le_iff₀ hDpos]
  calc (b + a * R) * (b * (1 - 2 * |R ^ (2 * n + 2) + r ^ (2 * n + 2) - 2|)
          + a * R * (1 - 2 * |R ^ (2 * n + 1) - r ^ (2 * n + 1)|))
      ≤ (b + a * (5 / 4)) ^ 2 := hnum
    _ ≤ (2 / 3) * (a * b ^ 2 * (27 / 8)) := harith
    _ ≤ (2 / 3) * (a * b ^ 2 * (R * r) ^ (2 * n) * (R + r) ^ 3) :=
        mul_le_mul_of_nonneg_left hD (by norm_num)

end Work.OddCurve.LowSlope
