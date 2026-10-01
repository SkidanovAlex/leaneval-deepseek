import Mathlib

namespace Work.LinnikAreas.TuranOther

/-! ### Term-level rewriting for log-multiplied L-series

We collect a few elementary facts used to convert the `k`-fold logarithmic derivative of an
L-series into the sum appearing in `reIteratedDerivLogDeriv`. -/

private lemma logMul_iterate_apply (f : ℕ → ℂ) (k n : ℕ) :
    (LSeries.logMul^[k] f) n = (Complex.log n)^k * f n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', LSeries.logMul, ih, pow_succ]; ring

private lemma re_mul_ofReal (r : ℝ) (w : ℂ) : ((r : ℂ) * w).re = r * w.re := by
  simp [Complex.mul_re]

/-- The `n`th term of the `k`-fold `log`-multiplied L-series of `f` at `s` has real part
`(log n)^k` times the real part of `f n · n^{-s}`, uniformly in `n ≠ 0` (for `n = 0` both
sides vanish as soon as `k ≠ 0`). -/
private lemma term_re (f : ℕ → ℂ) {k : ℕ} (hk : k ≠ 0) (s : ℂ) (n : ℕ) :
    (LSeries.term (LSeries.logMul^[k] f) s n).re
      = (Real.log n) ^ k * (f n * (n : ℂ) ^ (-s)).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term, zero_pow hk]
  · rw [LSeries.term_of_ne_zero hn, logMul_iterate_apply, ← Complex.natCast_log,
      ← Complex.ofReal_pow, ← Complex.ofReal_natCast, mul_div_assoc, div_eq_mul_inv,
      ← Complex.cpow_neg, re_mul_ofReal]

/-- The real part of the `k`-th derivative of the (negated) L-series of `f` at `s`, for odd `k`
and `re s` in the half-plane of absolute convergence, is the sum
`∑' n, (log n)^k * re (f n · n^{-s})`. -/
theorem reIteratedDerivLogDeriv {F : ℂ → ℂ} {f : ℕ → ℂ} (hF : Set.EqOn F (fun z => - LSeries f z) {z : ℂ | 1 < z.re}) (hab : LSeries.abscissaOfAbsConv f ≤ 1) {k : ℕ} (hk : k % 2 = 1) {s : ℂ} (hs : 1 < s.re) : (iteratedDeriv k F s).re = ∑' n : ℕ, (Real.log n) ^ k * (f n * (n : ℂ) ^ (-s)).re := by
  -- The half-plane `{re z > 1}` is open and contains `s`, so `F` agrees with `-LSeries f`
  -- in a whole neighbourhood of `s`.
  have hU : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  -- `re s` exceeds the abscissa of absolute convergence of `f`.
  have hb : LSeries.abscissaOfAbsConv f < (s.re : EReal) :=
    lt_of_le_of_lt hab (EReal.coe_lt_coe_iff.mpr hs)
  -- Replace `F` by the explicit function on the half-plane.
  have h1 : iteratedDeriv k F s = iteratedDeriv k (fun z => - LSeries f z) s :=
    (hF.iteratedDeriv_of_isOpen hU k) hs
  -- Pull the negation out of the iterated derivative.
  have h2 : iteratedDeriv k (fun z => - LSeries f z) s = - iteratedDeriv k (LSeries f) s :=
    iteratedDeriv_fun_neg k (LSeries f) s
  -- Compute the iterated derivative of the L-series itself.
  have h3 : iteratedDeriv k (LSeries f) s = (-1) ^ k * LSeries (LSeries.logMul^[k] f) s :=
    LSeries_iteratedDeriv k hb
  have hneg : (-1 : ℂ) ^ k = -1 := (Nat.odd_iff.mpr hk).neg_one_pow
  have hkey : iteratedDeriv k F s = LSeries (LSeries.logMul^[k] f) s := by
    rw [h1, h2, h3, hneg]; ring
  -- Summability of the terms, to move `re` through the infinite sum.
  have hsummable : Summable (LSeries.term (LSeries.logMul^[k] f) s) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (by rw [LSeries.absicssaOfAbsConv_logPowMul]; exact hb)
  rw [hkey]
  show (∑' n, LSeries.term (LSeries.logMul^[k] f) s n).re = _
  rw [Complex.re_tsum hsummable]
  exact tsum_congr (fun n => term_re f hk0 s n)

end Work.LinnikAreas.TuranOther
