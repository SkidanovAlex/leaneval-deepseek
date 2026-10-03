import Mathlib

namespace Work.Pert

/-! Real arithmetic needed by the gate-walk sum bound.  With `α = 33/32` (a real constant),
`A = α·n·r + 2`, `K = n + 1`, for `n ≥ 3` and `0 < r ≤ 1/2`:
`3 A K ≤ 30 (1 + n r) (1 + log (2+n)) (K - A)`.
(Verified numerically: the ratio LHS/RHS maxes at ≈ 0.48, at `n = 3`, `r = 1/2`; the RHS factors
are positive since `K - A = n - 1 - α n r ≥ 0.484 n - 1 > 0` for `n ≥ 3`, `r ≤ 1/2`.)

Proof outline.  Write `x = n` (a real ≥ 3) and keep the exact rational constants.  The needed
logarithmic factor is at least `2` because `2 + n ≥ 5 > e`.  It remains to show the purely
polynomial inequality
`3 A (x+1) ≤ 60 (1 + x r) (x+1 - A)`  (`A = (33/32) x r + 2`), for `3 ≤ x`, `0 < r ≤ 1/2`.
Since the difference of the two sides is a concave quadratic in `r`, it is at least the linear
interpolant of its endpoint values; the explicit decomposition proved in `key60` below exhibits
this difference as
`(1-2r)·f(0) + 2r·f(1/2) + 30·(33/32)·x²·r·(1-2r)`,
a sum of nonnegative terms (`f(0) = 54x - 66 ≥ 0` and `f(1/2) = (831x² - 543x - 4224)/64 ≥ 0` for
`x ≥ 3`). -/

/-- Core polynomial inequality: for `x ≥ 3`, `0 < r ≤ 1/2` and `A = (33/32) x r + 2`,
`3 A (x+1) ≤ 60 (1 + x r) (x+1 - A)`.  The difference of the two sides is a concave quadratic in
`r` with nonnegative value at both endpoints of `[0, 1/2]` (see the explicit decomposition). -/
private lemma key60 {x r : ℝ} (hx : 3 ≤ x) (hr0 : 0 < r) (hr : r ≤ 1 / 2) :
    3 * (x * (33 / 32 * r) + 2) * (x + 1)
      ≤ 60 * (1 + x * r) * (x + 1 - (x * (33 / 32 * r) + 2)) := by
  have h1 : 0 ≤ 1 - 2 * r := by linarith
  have h2 : 0 ≤ 2 * r := by linarith
  have h3 : 0 ≤ 54 * x - 66 := by linarith
  have h4 : 0 ≤ 831 * x ^ 2 - 543 * x - 4224 := by
    nlinarith [hx, sq_nonneg x,
      mul_nonneg (by linarith : (0 : ℝ) ≤ x) (by linarith : (0 : ℝ) ≤ x)]
  have hid : 60 * (1 + x * r) * (x + 1 - (x * (33 / 32 * r) + 2))
      - 3 * (x * (33 / 32 * r) + 2) * (x + 1)
      = (1 - 2 * r) * (54 * x - 66)
        + 2 * r * (831 * x ^ 2 - 543 * x - 4224) / 64
        + 30 * (33 / 32 : ℝ) * x ^ 2 * r * (1 - 2 * r) := by
    ring
  have t1 : 0 ≤ (1 - 2 * r) * (54 * x - 66) := mul_nonneg h1 h3
  have t2 : 0 ≤ 2 * r * ((831 * x ^ 2 - 543 * x - 4224) / 64) :=
    mul_nonneg h2 (by linarith)
  have t3 : 0 ≤ 30 * (33 / 32 : ℝ) * x ^ 2 * r * (1 - 2 * r) := by
    apply mul_nonneg
    apply mul_nonneg
    apply mul_nonneg
    · norm_num
    · positivity
    · exact le_of_lt hr0
    · linarith
  linarith [hid, t1, t2, t3]

theorem arith_theta {n : ℕ} (hn : 3 ≤ n) {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 1 / 2) :
    3 * ((n : ℝ) * ((33 / 32 : ℝ) * r) + 2) * ((n : ℝ) + 1)
      ≤ 30 * (1 + (n : ℝ) * r) * (1 + Real.log (2 + (n : ℝ)))
          * ((n : ℝ) + 1 - ((n : ℝ) * ((33 / 32 : ℝ) * r) + 2)) := by
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- `1 + log (2+n) ≥ 2` since `2+n ≥ 5 > e`.
  have he : Real.exp 1 < 2 + (n : ℝ) := lt_of_lt_of_le Real.exp_one_lt_three (by linarith)
  have hlog : (2 : ℝ) ≤ 1 + Real.log (2 + (n : ℝ)) := by
    have h : (1 : ℝ) < Real.log (2 + (n : ℝ)) :=
      (Real.lt_log_iff_exp_lt (by linarith : (0 : ℝ) < 2 + (n : ℝ))).mpr he
    linarith
  -- The constants and the core polynomial bound.
  have hkey := key60 hnR hr0 hr
  have hBpos : (0 : ℝ) < (n : ℝ) + 1 - ((n : ℝ) * ((33 / 32 : ℝ) * r) + 2) := by
    nlinarith [hnR, hr0, hr]
  have hLpos : (0 : ℝ) < 1 + (n : ℝ) * r := by nlinarith [hr0]
  have h30 : (0 : ℝ) ≤
      30 * (1 + (n : ℝ) * r) * ((n : ℝ) + 1 - ((n : ℝ) * ((33 / 32 : ℝ) * r) + 2)) := by
    nlinarith [hLpos, hBpos]
  have hprod : 0 ≤ (1 + Real.log (2 + (n : ℝ)) - 2)
      * (30 * (1 + (n : ℝ) * r) * ((n : ℝ) + 1 - ((n : ℝ) * ((33 / 32 : ℝ) * r) + 2))) :=
    mul_nonneg (by linarith) h30
  have hmul : 60 * (1 + (n : ℝ) * r) * ((n : ℝ) + 1 - ((n : ℝ) * ((33 / 32 : ℝ) * r) + 2))
      ≤ 30 * (1 + (n : ℝ) * r) * (1 + Real.log (2 + (n : ℝ)))
          * ((n : ℝ) + 1 - ((n : ℝ) * ((33 / 32 : ℝ) * r) + 2)) := by
    nlinarith [hprod]
  linarith [hkey, hmul]

end Work.Pert
