import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Repel.covering_near_id

/-!
# `Work.Repel.exists_piExp_eq_of_ball`

`π w = exp (2πi w)` (period `1`) is a local biholomorphism, so a small disc around `a` is carried
onto a neighbourhood of `π a`, of size comparable with `r · ‖(π)'(a)‖ = 2π r ‖π a‖`.  Here we
prove the quantitative form needed by the §6 assembly: for `r ≤ 1/100` the image of
`Metric.ball a r` covers `Metric.ball (π a) (r * ‖deriv π a‖ / 8)`.

The argument is elementary.  Writing `b = π a ≠ 0` and `q = z / b`, the desired preimage is
`w = a + log q / (2πi)` (`Complex.exp_log`), and it lies in `Metric.ball a r` because

* `‖z - b‖ < π r ‖b‖ / 4`, so `‖q - 1‖ = ‖z - b‖ / ‖b‖ < π r / 4 ≤ 1/2`, and
* `‖log q‖ = ‖log (1 + (q - 1))‖ ≤ (3/2) ‖q - 1‖ < (3/2)(π r / 4) = 3π r / 8 < 2π r`
  (`Complex.norm_log_one_add_half_le_self`), whence `‖log q / (2πi)‖ < 2π r / (2π) = r`.

In particular the sharp Koebe quarter theorem would give the same conclusion (with `4` in place of
`8`), but that route would drag in the area-theorem development, so we keep this self-contained.
-/

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology

/-- `(π)'(a) = 2πi · π a`, so `‖(π)'(a)‖ = 2π ‖π a‖`. -/
lemma norm_deriv_piExp (a : ℂ) :
    ‖deriv MandelDim.piExp a‖ = 2 * Real.pi * ‖MandelDim.piExp a‖ := by
  have h1 : HasDerivAt (fun w : ℂ => 2 * Real.pi * I * w) (2 * Real.pi * I) a := by
    simpa using (hasDerivAt_id a).const_mul (2 * Real.pi * I)
  have h2 : HasDerivAt (fun w : ℂ => Complex.exp (2 * Real.pi * I * w))
      (Complex.exp (2 * Real.pi * I * a) * (2 * Real.pi * I)) a :=
    (Complex.hasDerivAt_exp (2 * Real.pi * I * a)).comp a h1
  have hderiv : deriv MandelDim.piExp a = 2 * Real.pi * I * MandelDim.piExp a := by
    show deriv (fun w : ℂ => Complex.exp (2 * Real.pi * I * w)) a
      = 2 * Real.pi * I * Complex.exp (2 * Real.pi * I * a)
    rw [h2.deriv]
    ring
  rw [hderiv]
  have h3 : ‖(2 * Real.pi : ℂ) * I * MandelDim.piExp a‖
      = 2 * Real.pi * ‖MandelDim.piExp a‖ := by
    rw [norm_mul, norm_mul]
    simp [Complex.norm_I, Complex.norm_real]
  exact h3

/-- `π` is a multiplicative exponential: `π (x + y) = π x · π y`. -/
lemma piExp_add_ball (x y : ℂ) :
    MandelDim.piExp (x + y) = MandelDim.piExp x * MandelDim.piExp y := by
  have h : (2 * Real.pi * I) * (x + y) = (2 * Real.pi * I) * x + (2 * Real.pi * I) * y := by ring
  simp only [MandelDim.piExp]
  rw [h, Complex.exp_add]

/-- `π` inverts `log / (2πi)` on `ℂ \ {0}`. -/
lemma piExp_exp_log_div (q : ℂ) (hq : q ≠ 0) :
    MandelDim.piExp (Complex.log q / (2 * Real.pi * I)) = q := by
  have hne : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  simp only [MandelDim.piExp]
  rw [mul_div_cancel₀ _ hne, Complex.exp_log hq]

/-- `‖2πi‖ = 2π`. -/
lemma norm_two_pi_I : ‖(2 * Real.pi * I : ℂ)‖ = 2 * Real.pi := by
  rw [norm_mul, norm_mul]
  simp [Complex.norm_I, Complex.norm_real]

/-- **`π` covers a definite disc around `π a`.**  For `0 < r ≤ 1/100`, every point of
`Metric.ball (π a) (r * ‖deriv π a‖ / 8) = Metric.ball (π a) (π r ‖π a‖ / 4)` has a preimage under
`π` inside `Metric.ball a r`. -/
theorem exists_piExp_eq_of_ball {a z : ℂ} {r : ℝ} (hr : 0 < r) (hrle : r ≤ 1 / 100)
    (hz : z ∈ Metric.ball (MandelDim.piExp a) (r * ‖deriv MandelDim.piExp a‖ / 8)) :
    ∃ w ∈ Metric.ball a r, MandelDim.piExp w = z := by
  have hbne : MandelDim.piExp a ≠ 0 := Complex.exp_ne_zero _
  have hbpos : 0 < ‖MandelDim.piExp a‖ := norm_pos_iff.mpr hbne
  -- first convert the hypothesis into `‖z - π a‖ < π r ‖π a‖ / 4`
  have hzbd : ‖z - MandelDim.piExp a‖ < Real.pi * r * ‖MandelDim.piExp a‖ / 4 := by
    have h := Metric.mem_ball.mp hz
    rw [dist_eq_norm, norm_deriv_piExp] at h
    have heq : r * (2 * Real.pi * ‖MandelDim.piExp a‖) / 8
        = Real.pi * r * ‖MandelDim.piExp a‖ / 4 := by ring
    linarith
  -- hence `‖q - 1‖ < π r / 4` for `q = z / π a`
  have ht : ‖z / MandelDim.piExp a - 1‖ < Real.pi * r / 4 := by
    have h1 : z / MandelDim.piExp a - 1 = (z - MandelDim.piExp a) / MandelDim.piExp a := by
      field_simp
    rw [h1, norm_div, div_lt_iff₀ hbpos]
    have heq : Real.pi * r * ‖MandelDim.piExp a‖ / 4
        = (Real.pi * r / 4) * ‖MandelDim.piExp a‖ := by ring
    linarith
  have ht_le : ‖z / MandelDim.piExp a - 1‖ ≤ 1 / 2 := by
    have h : Real.pi * r / 4 ≤ 1 / 2 := by nlinarith [hrle, hr, Real.pi_lt_four]
    linarith
  have hqne : z / MandelDim.piExp a ≠ 0 := by
    intro h0
    have h1 : ‖z / MandelDim.piExp a - 1‖ = 1 := by rw [h0]; norm_num
    have h2 : Real.pi * r / 4 < 1 := by nlinarith [hrle, hr, Real.pi_lt_four]
    linarith
  -- the logarithmic bound
  have hlog := Complex.norm_log_one_add_half_le_self (z := z / MandelDim.piExp a - 1) ht_le
  rw [show (1 : ℂ) + (z / MandelDim.piExp a - 1) = z / MandelDim.piExp a by ring] at hlog
  have hloglt : ‖Complex.log (z / MandelDim.piExp a)‖ < 2 * Real.pi * r := by
    nlinarith [hlog, ht, hr, Real.pi_pos]
  refine ⟨a + Complex.log (z / MandelDim.piExp a) / (2 * Real.pi * I), ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_div, norm_two_pi_I,
      div_lt_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi)]
    linarith
  · rw [piExp_add_ball, piExp_exp_log_div _ hqne]
    exact mul_div_cancel₀ z hbne

end Work.Repel
