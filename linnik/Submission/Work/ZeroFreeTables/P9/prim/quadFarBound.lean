import Mathlib

namespace Work.ZeroFreeTables.P9.prim

/-- The "far" point `1 + i·Im s - u` is at distance at least `δ` from `u`, and
`Re s > 1 > Re u` forces `s - u` to have the same imaginary part but larger real
part, hence `‖s - u‖ > δ`. -/
lemma norm_far_lt {s u : ℂ} {δ : ℝ} (hδ : 0 < δ) (hs : 1 < s.re) (hu : u.re < 1)
    (hfar : δ < ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖) : δ < ‖s - u‖ := by
  have hre : ((1:ℂ) + (s.im:ℂ)*Complex.I - u).re = 1 - u.re := by
    simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  have him : ((1:ℂ) + (s.im:ℂ)*Complex.I - u).im = s.im - u.im := by
    simp [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  have hfarVal : Complex.normSq ((1:ℂ) + (s.im:ℂ)*Complex.I - u)
      = (1 - u.re)^2 + (s.im - u.im)^2 := by
    rw [Complex.normSq_apply, hre, him]; ring
  have hsVal : Complex.normSq (s - u) = (s.re - u.re)^2 + (s.im - u.im)^2 := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]; ring
  have hfarSq : δ ^ 2 < Complex.normSq ((1:ℂ) + (s.im:ℂ)*Complex.I - u) := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_lt_pow_left₀ hfar (le_of_lt hδ) (by norm_num)
  have hfarSq2 : δ^2 < (1 - u.re)^2 + (s.im - u.im)^2 := by rw [hfarVal] at hfarSq; exact hfarSq
  have ha : 0 < 1 - u.re := by linarith
  have hb : 1 - u.re < s.re - u.re := by linarith
  have hsq : (1 - u.re)^2 < (s.re - u.re)^2 := by nlinarith [ha, hb]
  have hsq2 : δ^2 < (s.re - u.re)^2 + (s.im - u.im)^2 := by linarith [hfarSq2, hsq]
  have hsqδ : δ^2 < ‖s - u‖^2 := by rw [Complex.sq_norm, hsVal]; exact hsq2
  exact (sq_lt_sq₀ (le_of_lt hδ) (norm_nonneg _)).mp hsqδ

theorem quadFarBound {s u : ℂ} {δ : ℝ} (hδ : 0 < δ) (hs : 1 < s.re) (hu : u.re < 1)
    (hfar : δ < ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖) :
    -((1 + 4 / δ ^ 2) / (1 + ‖s - u‖ ^ 2)) ≤ ((1 / (s - u)) ^ 2).re := by
  have hnorm : δ < ‖s - u‖ := norm_far_lt hδ hs hu hfar
  have hnormpos : 0 < ‖s - u‖ := lt_trans hδ hnorm
  have hsqδ : δ^2 < ‖s - u‖^2 := pow_lt_pow_left₀ hnorm (le_of_lt hδ) (by norm_num)
  have hrpos : 0 < ‖s - u‖^2 := pow_pos hnormpos 2
  have hcpos : (0:ℝ) < 4 / δ^2 := by positivity
  have hcr : (4/δ^2) * δ^2 = 4 := div_mul_cancel₀ 4 (pow_pos hδ 2).ne'
  have hlt : (4:ℝ) < (4/δ^2) * ‖s - u‖^2 := by
    have h0 := mul_lt_mul_of_pos_left hsqδ hcpos
    rw [hcr] at h0
    exact h0
  have hr1pos : 0 < 1 + ‖s - u‖^2 := by linarith
  have hmain2 : (1:ℝ) / ‖s - u‖^2 ≤ (1 + 4/δ^2) / (1 + ‖s - u‖^2) := by
    rw [div_le_iff₀ hrpos, div_mul_eq_mul_div, le_div_iff₀ hr1pos]
    nlinarith [hlt]
  have hnormeq : ‖(1 / (s - u))^2‖ = 1 / ‖s - u‖^2 := by
    rw [norm_pow, norm_div, norm_one, div_pow, one_pow]
  have hz : -‖(1 / (s - u))^2‖ ≤ ((1 / (s - u))^2).re := by
    have h1 := Complex.abs_re_le_norm ((1 / (s - u))^2)
    have h2 := neg_abs_le ((1 / (s - u))^2).re
    linarith
  have hstep1 : -((1 + 4/δ^2) / (1 + ‖s - u‖ ^ 2)) ≤ -(1 / ‖s - u‖^2) := neg_le_neg hmain2
  have hstep2 : -(1 / ‖s - u‖^2) ≤ ((1 / (s - u))^2).re := by rw [← hnormeq]; exact hz
  exact le_trans hstep1 hstep2

end Work.ZeroFreeTables.P9.prim
