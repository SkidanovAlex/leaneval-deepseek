import Mathlib

namespace Work.FIArea3.JointCount

open Complex

/-- For a complex number `w` of norm `< 1`, the argument of `1 + w` is bounded by
`π/2 * ‖w‖`. This is the quantitative form of "`1 + w` stays in the right half plane". -/
private lemma im_sq_le (w : ℂ) : w.im ^ 2 ≤ (‖w‖ * ‖(1 + w : ℂ)‖) ^ 2 := by
  rw [mul_pow, Complex.sq_norm, Complex.sq_norm]
  rw [Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, zero_add]
  nlinarith [sq_nonneg (w.re + (w.re * w.re + w.im * w.im))]

private lemma abs_arg_one_add_le (w : ℂ) {ρ : ℝ} (hρw : ‖w‖ ≤ ρ) (hw1 : ‖w‖ < 1) :
    |Complex.arg (1 + w)| ≤ Real.pi / 2 * ρ := by
  have ht_ne : (1 + w : ℂ) ≠ 0 := by
    intro h
    have hw : w = -1 := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact h
    have : ‖w‖ = 1 := by rw [hw]; simp
    linarith
  have ht_norm_pos : 0 < ‖(1 + w : ℂ)‖ := norm_pos_iff.mpr ht_ne
  have hre : 0 ≤ (1 + w : ℂ).re := by
    have h1 : (1 + w : ℂ).re = 1 + w.re := by simp
    rw [h1]
    have h2 : -(‖w‖) ≤ w.re := (abs_le.mp (Complex.abs_re_le_norm w)).1
    linarith
  have harg_le : |Complex.arg (1 + w)| ≤ Real.pi / 2 := by
    rw [Complex.abs_arg_le_pi_div_two_iff]; exact hre
  have hJ : 2 / Real.pi * |Complex.arg (1 + w)| ≤ Real.sin |Complex.arg (1 + w)| :=
    Real.mul_le_sin (abs_nonneg (Complex.arg (1 + w))) harg_le
  have hsin_abs : Real.sin |Complex.arg (1 + w)| = |Real.sin (Complex.arg (1 + w))| := by
    rw [eq_comm, Real.abs_sin_eq_sin_abs_of_abs_le_pi]
    exact Complex.abs_arg_le_pi (1 + w)
  rw [hsin_abs] at hJ
  have hsin_eq : |Real.sin (Complex.arg (1 + w))| = |(1 + w : ℂ).im| / ‖(1 + w : ℂ)‖ := by
    rw [Complex.sin_arg, abs_div, abs_of_nonneg (norm_nonneg _)]
  rw [hsin_eq] at hJ
  have h_im : (1 + w : ℂ).im = w.im := by simp
  have hbound : |(1 + w : ℂ).im| / ‖(1 + w : ℂ)‖ ≤ ‖w‖ := by
    rw [h_im, div_le_iff₀ ht_norm_pos]
    exact abs_le_of_sq_le_sq (im_sq_le w) (by positivity)
  have step : 2 / Real.pi * |Complex.arg (1 + w)| ≤ ‖w‖ := le_trans hJ hbound
  have hp2 : (0:ℝ) < Real.pi / 2 := by positivity
  have hmul : Real.pi / 2 * (2 / Real.pi * |Complex.arg (1 + w)|) ≤ Real.pi / 2 * ‖w‖ :=
    mul_le_mul_of_nonneg_left step hp2.le
  have hsimp : Real.pi / 2 * (2 / Real.pi * |Complex.arg (1 + w)|) =
      |Complex.arg (1 + w)| := by
    field_simp
  rw [hsimp] at hmul
  calc |Complex.arg (1 + w)| ≤ Real.pi / 2 * ‖w‖ := hmul
    _ ≤ Real.pi / 2 * ρ := mul_le_mul_of_nonneg_left hρw hp2.le

theorem arg_add_sub_mem_Icc (z u : ℂ) (a r : ℝ) (ha : 0 < a) (hr0 : 0 ≤ r) (hr1 : r ≤ a)
    (hz : a < ‖z‖) (hu : ‖u‖ ≤ r) :
    ∃ k : ℤ, Complex.arg (z + u) + 2 * Real.pi * k ∈
      Set.Icc (Complex.arg z - Real.pi / 2 * (r / a)) (Complex.arg z + Real.pi / 2 * (r / a)) := by
  have hza : a ≤ ‖z‖ := hz.le
  have hzpos : 0 < ‖z‖ := lt_trans ha hz
  have hzne : z ≠ 0 := norm_pos_iff.mp hzpos
  set w : ℂ := u / z with hwdef
  have hw_norm : ‖w‖ = ‖u‖ / ‖z‖ := by rw [hwdef, Complex.norm_div]
  have hw_le : ‖w‖ ≤ r / a := by
    rw [hw_norm]
    calc ‖u‖ / ‖z‖ ≤ r / ‖z‖ := div_le_div_of_nonneg_right hu (norm_nonneg z)
      _ ≤ r / a := div_le_div_of_nonneg_left hr0 ha hza
  have hw1 : ‖w‖ < 1 := by
    rw [hw_norm]
    have hlt : ‖u‖ < ‖z‖ := lt_of_le_of_lt hu (lt_of_le_of_lt hr1 hz)
    exact (div_lt_one hzpos).mpr hlt
  have h1w : (1 + w : ℂ) ≠ 0 := by
    intro h
    have hw : w = -1 := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h
    have : ‖w‖ = 1 := by rw [hw]; simp
    linarith
  have hbound : |Complex.arg (1 + w)| ≤ Real.pi / 2 * (r / a) :=
    abs_arg_one_add_le w hw_le hw1
  have hmul : z * (1 + w) = z + u := by rw [hwdef]; field_simp
  have hAngle : (Complex.arg (z + u) : Real.Angle) =
      ((Complex.arg z + Complex.arg (1 + w) : ℝ) : Real.Angle) := by
    rw [← hmul, Complex.arg_mul_coe_angle hzne h1w, Real.Angle.coe_add]
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hAngle
  refine ⟨-k, ?_⟩
  have hkey : Complex.arg (z + u) + 2 * Real.pi * ((-k : ℤ) : ℝ) =
      Complex.arg z + Complex.arg (1 + w) := by
    have : ((-k : ℤ) : ℝ) = -(k : ℝ) := by push_cast; ring
    rw [this]
    linarith [hk]
  rw [Set.mem_Icc, hkey]
  constructor
  · have := neg_abs_le (Complex.arg (1 + w)); linarith
  · have := le_abs_self (Complex.arg (1 + w)); linarith

end Work.FIArea3.JointCount
