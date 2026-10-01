import Mathlib

namespace Work.LinnikAreas.FarRepel

private lemma logMul_iterate_apply (f : ℕ → ℂ) (k n : ℕ) :
    (LSeries.logMul^[k] f) n = (Complex.log n)^k * f n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', LSeries.logMul, ih, pow_succ]; ring

private lemma re_mul_ofReal (r : ℝ) (w : ℂ) : ((r : ℂ) * w).re = r * w.re := by
  simp [Complex.mul_re]

/-- The `n`-th term of the `k`-fold `log`-multiplied L-series of `f` at `s` has real part
`(log n)^k` times the real part of `f n · n^{-s}` (for `n ≠ 0`). -/
theorem reTermLogMulIterate {f : ℕ → ℂ} (k : ℕ) (s : ℂ) {n : ℕ} (hn : n ≠ 0) :
    (LSeries.term (LSeries.logMul ^[k] f) s n).re
      = (Real.log n) ^ k * (f n * (n : ℂ) ^ (-s)).re := by
  rw [LSeries.term_of_ne_zero hn, logMul_iterate_apply, ← Complex.natCast_log,
    ← Complex.ofReal_pow, ← Complex.ofReal_natCast, mul_div_assoc]
  rw [div_eq_mul_inv, ← Complex.cpow_neg, re_mul_ofReal]

end Work.LinnikAreas.FarRepel
