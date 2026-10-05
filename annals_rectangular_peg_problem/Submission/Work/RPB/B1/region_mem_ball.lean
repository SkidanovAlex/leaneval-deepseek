import Mathlib

namespace Work.RPB.B1

/-- A point at height `y` and abscissa `r` lies strictly to the left of `x` on the circle of
radius `R` centred at `(x, y)` — equivalently `(r - x)² + y² < R²` — exactly when
`r < x + √(R² - y²)`, provided `0 < r` and `x² + y² < R²` (so the ray at height `y` meets the
circle and the left intersection `x - √(R² - y²)` is negative). -/
lemma real_lt_sqrt_iff (R x y r : ℝ) (hxy : x ^ 2 + y ^ 2 < R ^ 2) (hr : 0 < r) :
    ((r - x) ^ 2 + y ^ 2 < R ^ 2 ↔ r < x + Real.sqrt (R ^ 2 - y ^ 2)) := by
  have hy2 : 0 < R ^ 2 - y ^ 2 := by nlinarith [sq_nonneg x]
  have hs2 : Real.sqrt (R ^ 2 - y ^ 2) ^ 2 = R ^ 2 - y ^ 2 := Real.sq_sqrt (le_of_lt hy2)
  have hsnn : 0 ≤ Real.sqrt (R ^ 2 - y ^ 2) := Real.sqrt_nonneg _
  have hxs : x < Real.sqrt (R ^ 2 - y ^ 2) := by
    have h1 : Real.sqrt (x ^ 2) < Real.sqrt (R ^ 2 - y ^ 2) :=
      Real.sqrt_lt_sqrt (sq_nonneg x) (by nlinarith)
    rw [Real.sqrt_sq_eq_abs] at h1
    linarith [le_abs_self x]
  have hkey : |r - x| < Real.sqrt (R ^ 2 - y ^ 2) ↔ (r - x) ^ 2 < R ^ 2 - y ^ 2 := by
    rw [show Real.sqrt (R ^ 2 - y ^ 2) = |Real.sqrt (R ^ 2 - y ^ 2)| from
      (abs_of_nonneg hsnn).symm, ← sq_lt_sq, hs2]
  constructor
  · intro h
    have h2 : (r - x) ^ 2 < R ^ 2 - y ^ 2 := by nlinarith [sq_nonneg y]
    have h3 := hkey.mpr h2
    have := (abs_lt.mp h3).2
    linarith
  · intro h
    have h1 : -(Real.sqrt (R ^ 2 - y ^ 2)) < r - x := by linarith
    have h2 : r - x < Real.sqrt (R ^ 2 - y ^ 2) := by linarith
    have h3 : |r - x| < Real.sqrt (R ^ 2 - y ^ 2) := abs_lt.mpr ⟨h1, h2⟩
    have h4 := hkey.mp h3
    linarith

/-- The polar point `r e^{iφ}` lies in the disc `ball a R` exactly when its radius `r` is smaller
than the radial extent `Re (a e^{-iφ}) + √(R² - Im (a e^{-iφ})²)` of that disc in the direction
`e^{iφ}`.  Here `‖a‖ < R` (the pole is inside the disc) and `r > 0` (so the other intersection of
the ray with the circle is automatically on the negative ray). -/
lemma polar_exp_mem_ball_iff (a : ℂ) {R r φ : ℝ} (hR : ‖a‖ < R) (hr : 0 < r) :
    ((r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) ∈ Metric.ball a R ↔
      r < (a * Complex.exp (-(φ : ℂ) * Complex.I)).re
        + Real.sqrt (R ^ 2 - (a * Complex.exp (-(φ : ℂ) * Complex.I)).im ^ 2) := by
  set b : ℂ := a * Complex.exp (-(φ : ℂ) * Complex.I) with hb
  have hRpos : 0 < R := lt_of_le_of_lt (norm_nonneg a) hR
  have hexp : ‖Complex.exp (-(φ : ℂ) * Complex.I)‖ = 1 := by
    rw [show -(φ : ℂ) * Complex.I = ((-φ : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have hbnorm : ‖b‖ = ‖a‖ := by
    rw [hb, Complex.norm_mul, hexp, mul_one]
  have hbsq : b.re ^ 2 + b.im ^ 2 < R ^ 2 := by
    have h : ‖b‖ ^ 2 = b.re ^ 2 + b.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have hnorm2 : ‖a‖ ^ 2 < R ^ 2 := by
      rw [sq_lt_sq, abs_of_nonneg (norm_nonneg a), abs_of_pos hRpos]
      exact hR
    rw [← h, hbnorm]
    exact hnorm2
  have hnorm : ‖(r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) - a‖ = ‖(r : ℂ) - b‖ := by
    have h1 : ((r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) - a)
        * Complex.exp (-(φ : ℂ) * Complex.I) = (r : ℂ) - b := by
      rw [hb, sub_mul, mul_assoc, ← Complex.exp_add, neg_mul, add_neg_cancel, Complex.exp_zero,
        mul_one]
    rw [← h1, Complex.norm_mul, hexp, mul_one]
  have hsq : ‖(r : ℂ) - b‖ ^ 2 = (r - b.re) ^ 2 + b.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hlt : ‖(r : ℂ) - b‖ < R ↔ (r - b.re) ^ 2 + b.im ^ 2 < R ^ 2 := by
    rw [← hsq, sq_lt_sq, abs_of_pos hRpos, abs_of_nonneg (norm_nonneg ((r : ℂ) - b))]
  rw [Metric.mem_ball, dist_eq_norm, hnorm, hlt]
  exact real_lt_sqrt_iff R b.re b.im r hbsq hr

theorem region_mem_ball (a : ℂ) {R : ℝ} (hR : ‖a‖ < R) (p : ℝ × ℝ) (hp1 : 0 < p.1) :
    Complex.polarCoord.symm p ∈ Metric.ball a R ↔
      p.1 < (a * Complex.exp (-(p.2 : ℂ) * Complex.I)).re
        + Real.sqrt (R ^ 2 - (a * Complex.exp (-(p.2 : ℂ) * Complex.I)).im ^ 2) := by
  rw [show (Complex.polarCoord.symm p : ℂ)
      = (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I) from by
    rw [Complex.polarCoord_symm_apply, Complex.exp_ofReal_mul_I]]
  exact polar_exp_mem_ball_iff a hR hp1

end Work.RPB.B1
