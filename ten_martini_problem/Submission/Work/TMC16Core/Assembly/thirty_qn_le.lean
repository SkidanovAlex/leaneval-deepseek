import Mathlib

namespace Work.TMC16Core.Assembly

/-! ## The `30 · q n ≤ q (n+1)` arithmetic step

Given `q n ≥ 66^8`, and a real `y` sandwiched as `(q n)/2 ≤ y ≤ (q (n+1))^(8/9)`,
we prove `30 · q n ≤ q (n+1)`.

The constant `66^8` is exactly what makes the numeric bound `30 · 2^(9/8) ≤ 66`
(equivalently `2^(1/8) ≤ 11/10`) work: raising `(q n)/2 ≤ (q (n+1))^(8/9)` to the
power `9/8` gives `q (n+1) ≥ ((q n)/2)^(9/8) = q n · (q n)^(1/8) / 2^(9/8)`, and
`(q n)^(1/8) ≥ 66`. -/

/-- `2^(1/8) ≤ 11/10`, an elementary numeric fact obtained by raising to the 8th
power (`2 ≤ (11/10)^8`). -/
private lemma two_rpow_one_eighth_le : (2:ℝ)^((1:ℝ)/8) ≤ 11/10 := by
  have hbase : (2:ℝ) ≤ (11/10:ℝ)^8 := by norm_num
  have key : (2:ℝ)^((1:ℝ)/8) ≤ ((11/10:ℝ)^8)^((1:ℝ)/8) :=
    Real.rpow_le_rpow (by norm_num) hbase (by norm_num)
  have hkey : ((11/10:ℝ)^8)^((1:ℝ)/8) = 11/10 := by
    rw [show ((11/10:ℝ)^8) = (11/10:ℝ)^((8:ℕ):ℝ) from (Real.rpow_natCast (11/10) 8).symm]
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 11/10)]
    rw [show (((8:ℕ):ℝ) * ((1:ℝ)/8)) = 1 by norm_num, Real.rpow_one]
  rwa [hkey] at key

/-- The numeric inequality `30 ≤ 66 · (1/2)^(9/8)`, i.e. `30 · 2^(9/8) ≤ 66`,
following from `2^(1/8) ≤ 11/10`. -/
private lemma num_thirty : (30:ℝ) ≤ 66 * (1/2:ℝ)^((9:ℝ)/8) := by
  have h2 := two_rpow_one_eighth_le
  have h9 : (2:ℝ)^((9:ℝ)/8) = 2 * 2^((1:ℝ)/8) := by
    rw [show (9:ℝ)/8 = 1 + 1/8 by norm_num,
        Real.rpow_add (by norm_num : (0:ℝ) < 2), Real.rpow_one]
  have h66 : (30:ℝ) * 2^((9:ℝ)/8) ≤ 66 := by
    rw [h9]; nlinarith [h2]
  have hc : (0:ℝ) ≤ (1/2:ℝ)^((9:ℝ)/8) := Real.rpow_nonneg (by norm_num) _
  have hmul := mul_le_mul_of_nonneg_right h66 hc
  have hsimp : (2:ℝ)^((9:ℝ)/8) * (1/2:ℝ)^((9:ℝ)/8) = 1 := by
    rw [← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (0:ℝ) ≤ 1/2)]
    rw [show (2:ℝ) * (1/2) = 1 by norm_num, Real.one_rpow]
  have hL : (30:ℝ) * 2^((9:ℝ)/8) * (1/2:ℝ)^((9:ℝ)/8) = 30 := by
    rw [mul_assoc, hsimp, mul_one]
  rwa [hL] at hmul

theorem thirty_qn_le {q : ℕ → ℕ} {n : ℕ} {y : ℝ}
    (hqn : 66 ^ 8 ≤ q n) (hy : (q n : ℝ) / 2 ≤ y)
    (hyb : y ≤ Real.rpow (q (n + 1) : ℝ) ((8 : ℝ) / 9)) :
    (30 : ℝ) * (q n : ℝ) ≤ (q (n + 1) : ℝ) := by
  set A : ℝ := (q n : ℝ) with hA
  set B : ℝ := (q (n + 1) : ℝ) with hB
  have hA8 : (66:ℝ)^8 ≤ A := by rw [hA]; exact_mod_cast hqn
  have hAnn : (0:ℝ) ≤ A := le_trans (by norm_num) hA8
  have hApos : (0:ℝ) < A := lt_of_lt_of_le (by norm_num) hA8
  have hBnn : (0:ℝ) ≤ B := by rw [hB]; positivity
  have h1 : A / 2 ≤ B ^ ((8:ℝ)/9) := le_trans hy hyb
  -- Raise `(q n)/2 ≤ (q (n+1))^(8/9)` to the power `9/8`.
  have h2 : (A/2)^((9:ℝ)/8) ≤ B := by
    have hstep : (A/2)^((9:ℝ)/8) ≤ (B^((8:ℝ)/9))^((9:ℝ)/8) :=
      Real.rpow_le_rpow (div_nonneg hAnn (by norm_num)) h1 (by norm_num)
    have hBB : (B^((8:ℝ)/9))^((9:ℝ)/8) = B := by
      rw [← Real.rpow_mul hBnn]
      rw [show (8:ℝ)/9 * ((9:ℝ)/8) = 1 by norm_num, Real.rpow_one]
    rwa [hBB] at hstep
  -- `(q n)^(1/8) ≥ 66` from `q n ≥ 66^8`.
  have hroot : (66:ℝ) ≤ A^((1:ℝ)/8) := by
    have h1a : ((66:ℝ)^8)^((1:ℝ)/8) ≤ A^((1:ℝ)/8) :=
      Real.rpow_le_rpow (by norm_num) hA8 (by norm_num)
    have h2a : ((66:ℝ)^8)^((1:ℝ)/8) = 66 := by
      rw [show ((66:ℝ)^8) = (66:ℝ)^((8:ℕ):ℝ) from (Real.rpow_natCast (66:ℝ) 8).symm]
      rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 66)]
      rw [show (((8:ℕ):ℝ) * ((1:ℝ)/8)) = 1 by norm_num, Real.rpow_one]
    rwa [h2a] at h1a
  -- Split `((q n)/2)^(9/8) = q n · (q n)^(1/8) · (1/2)^(9/8)`.
  have hsplit : (A/2)^((9:ℝ)/8) = A * A^((1:ℝ)/8) * (1/2:ℝ)^((9:ℝ)/8) := by
    rw [show A/2 = A * (1/2) by ring, Real.mul_rpow hAnn (by norm_num : (0:ℝ) ≤ 1/2)]
    rw [show A^((9:ℝ)/8) = A * A^((1:ℝ)/8) by
      rw [show (9:ℝ)/8 = 1 + 1/8 by norm_num, Real.rpow_add hApos, Real.rpow_one]]
  have hstep2 : A * 66 * (1/2:ℝ)^((9:ℝ)/8) ≤ (A/2)^((9:ℝ)/8) := by
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hroot hAnn)
      (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) _)
  have h30 : (30:ℝ) * A ≤ A * 66 * (1/2:ℝ)^((9:ℝ)/8) := by
    have hh := mul_le_mul_of_nonneg_right num_thirty hAnn
    nlinarith [hh]
  exact le_trans (le_trans h30 hstep2) h2

end Work.TMC16Core.Assembly
