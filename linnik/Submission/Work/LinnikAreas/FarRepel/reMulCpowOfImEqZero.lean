import Mathlib

namespace Work.LinnikAreas.FarRepel

/-- For a non-zero natural `n`, the real part of `n^{-s}` is `n^{-Re s} cos(Im s · log n)`; more
generally the real part of `c * n^{-s}` depends only on `Re c` when `Im c = 0`. -/
theorem reMulCpowOfImEqZero {c : ℂ} (hc : c.im = 0) {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    (c * (n : ℂ) ^ (-s)).re = c.re * (n : ℝ) ^ (-s.re) * Real.cos (s.im * Real.log n) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [Complex.mul_re, hc, zero_mul, sub_zero, mul_assoc]
  congr 1
  rw [Complex.cpow_def_of_ne_zero hnc, ← Complex.ofReal_natCast n, ← Complex.ofReal_log hnpos.le,
    Complex.exp_re, Complex.re_ofReal_mul, Complex.neg_re, Complex.im_ofReal_mul, Complex.neg_im,
    Real.rpow_def_of_pos hnpos]
  congr 1
  rw [show Real.log (n : ℝ) * -s.im = -(s.im * Real.log (n : ℝ)) by ring, Real.cos_neg]

end Work.LinnikAreas.FarRepel
