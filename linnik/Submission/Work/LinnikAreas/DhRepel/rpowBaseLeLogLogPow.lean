import Mathlib

namespace Work.LinnikAreas.DhRepel

/-- For `q` with `L := log q ≥ 100`, and `t ≥ 0` with `3 t ≤ log (log (log q))`,
the real power `(q * (10 * log q)) ^ (3 t / log q)` is at most `(log (log q)) ^ 11`.

Write `L = log q`, `K = log L`, `A = log K`; then `3 t ≤ A` and the base is
`q * (10 L) = exp (L + log (10 L))`.  Hence the left side equals
`exp ((L + log (10 L)) * (3 t / L))`, and since `L + log (10 L) ≤ 11 L` we get
`(L + log (10 L)) * (3 t / L) ≤ (11 L) * (3 t / L) = 33 t ≤ 11 A`,
which is at most `11 log K`, so the expression is at most `exp (11 log K) = K ^ 11`. -/
theorem rpowBaseLeLogLogPow (q : ℕ) (t : ℝ)
    (hL : 100 ≤ Real.log (q : ℝ)) (ht0 : 0 ≤ t)
    (htZ : 3 * t ≤ Real.log (Real.log (Real.log (q : ℝ)))) :
    ((q : ℝ) * (10 * Real.log (q : ℝ))) ^ (3 * t / Real.log (q : ℝ))
      ≤ (Real.log (Real.log (q : ℝ))) ^ 11 := by
  set L : ℝ := Real.log (q : ℝ) with hLdef
  set K : ℝ := Real.log L with hKdef
  set AK : ℝ := Real.log K with hAKdef
  have hLpos : 0 < L := by linarith
  have hqne : (q : ℝ) ≠ 0 := by
    intro h
    have hzero : L = 0 := by rw [hLdef, h, Real.log_zero]
    linarith
  have hqpos : 0 < (q : ℝ) :=
    lt_of_le_of_ne (Nat.cast_nonneg q) (Ne.symm hqne)
  have h10Lpos : 0 < 10 * L := by linarith
  have hbase : 0 < (q : ℝ) * (10 * L) := mul_pos hqpos h10Lpos
  have hKpos : 0 < K := by
    apply Real.log_pos
    linarith
  have hlogbase : Real.log ((q : ℝ) * (10 * L)) = L + Real.log (10 * L) := by
    rw [Real.log_mul hqne (ne_of_gt h10Lpos), ← hLdef]
  have hlog10L_le : L + Real.log (10 * L) ≤ 11 * L := by
    have h := Real.log_le_sub_one_of_pos h10Lpos
    linarith
  have h1 : (3 * t / L) * (L + Real.log (10 * L)) ≤ (3 * t / L) * (11 * L) :=
    mul_le_mul_of_nonneg_left hlog10L_le
      (div_nonneg (by linarith : 0 ≤ 3 * t) (le_of_lt hLpos))
  have h2 : (3 * t / L) * (11 * L) = 33 * t := by
    field_simp
    ring
  have hkey : Real.log ((q : ℝ) * (10 * L)) * (3 * t / L) ≤ AK * 11 := by
    rw [hlogbase, mul_comm (L + Real.log (10 * L)) (3 * t / L)]
    have h4 : 33 * t ≤ AK * 11 := by linarith
    exact le_trans h1 (h2 ▸ h4)
  have hKpow : K ^ 11 = Real.exp (Real.log K * 11) := by
    rw [← Real.rpow_natCast K 11, Real.rpow_def_of_pos hKpos]
    norm_num
  rw [Real.rpow_def_of_pos hbase, hKpow, Real.exp_le_exp, ← hAKdef]
  exact hkey

end Work.LinnikAreas.DhRepel
