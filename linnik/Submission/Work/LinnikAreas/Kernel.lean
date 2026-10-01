import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Commons.NumberTheory.Linnik.norm_one_sub_exp_neg_le

/-!
# Elementary pointwise bounds for the Heath-Brown kernel

In Heath-Brown's §13 the far zeros are controlled by the two pointwise bounds

`‖F₂(z)‖ ≤ min(K², 4/‖z‖²)`  (for `Re z ≥ 0`),  hence
`‖Hk L K z‖ ≤ e^{-(L-2K)·Re z} · min(K², 4/‖z‖²)`,

where `F₂(z) = ((1-e^{-Kz})/z)²` and `Hk L K z = e^{-(L-2K)z}F₂(z)`
(`Submission.Work.LinnikContract.Defs`).  For a non-trivial zero `ρ` of `L(s,χ)` in the
critical strip, `z = (1-ρ)·log q` has `Re z = λ(ρ) ≥ 0`, so both bounds apply; the first is
used for the low (`λ ≲ 1`) zeros and the second for the high ones.
-/

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas

open Work.LinnikContract

lemma norm_one_sub_exp_le_two {z : ℂ} (hz : z.re ≤ 0) : ‖1 - Complex.exp z‖ ≤ 2 := by
  have hE : ‖Complex.exp z‖ ≤ 1 := by
    rw [Complex.norm_exp]; exact Real.exp_le_one_iff.mpr hz
  calc ‖1 - Complex.exp z‖ ≤ ‖(1 : ℂ)‖ + ‖Complex.exp z‖ := norm_sub_le 1 _
    _ = 1 + ‖Complex.exp z‖ := by simp
    _ ≤ 2 := by linarith

lemma F2_apply_zero (K : ℝ) : F2 K 0 = 0 := by
  simp [F2]

/-- `‖F₂(z)‖ ≤ K²` for `Re z ≥ 0`, since `‖1 - e^{-w}‖ ≤ ‖w‖` there. -/
lemma norm_F2_le_sq {K : ℝ} (hK : 0 < K) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖F2 K z‖ ≤ K ^ 2 := by
  rcases eq_or_ne z 0 with hz0 | hz0
  · subst hz0
    rw [F2_apply_zero, norm_zero]
    positivity
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hw : 0 ≤ ((K : ℂ) * z).re := by
      rw [Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact mul_nonneg (le_of_lt hK) hz
    have h1 := Commons.NumberTheory.Linnik.norm_one_sub_exp_neg_le ((K : ℂ) * z) hw
    have harg : -((K : ℂ) * z) = -(K : ℂ) * z := by ring
    rw [harg] at h1
    have hnorm : ‖(K : ℂ) * z‖ = K * ‖z‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hK]
    have h2 : ‖1 - Complex.exp (-(K : ℂ) * z)‖ / ‖z‖ ≤ K := by
      rw [div_le_iff₀ hn]
      calc ‖1 - Complex.exp (-(K : ℂ) * z)‖ ≤ ‖(K : ℂ) * z‖ := h1
        _ = K * ‖z‖ := hnorm
    calc ‖F2 K z‖ = (‖1 - Complex.exp (-(K : ℂ) * z)‖ / ‖z‖) ^ 2 := by
          rw [F2, norm_pow, norm_div]
      _ ≤ K ^ 2 := pow_le_pow_left₀ (by positivity) h2 2

/-- `‖F₂(z)‖ ≤ 4/‖z‖²` for `Re z ≥ 0` (the numerator is bounded by `2`). -/
lemma norm_F2_le_inv_sq {K : ℝ} (hK : 0 < K) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖F2 K z‖ ≤ 4 / ‖z‖ ^ 2 := by
  rcases eq_or_ne z 0 with hz0 | hz0
  · subst hz0
    rw [F2_apply_zero, norm_zero]
    norm_num
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hw : (-(K : ℂ) * z).re ≤ 0 := by
      have h : (-(K : ℂ) * z).re = -(K * z.re) := by
        simp only [Complex.neg_re, Complex.mul_re, Complex.neg_im, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero, neg_zero]
        ring
      rw [h]
      exact neg_nonpos_of_nonneg (mul_nonneg (le_of_lt hK) hz)
    have h2 : ‖1 - Complex.exp (-(K : ℂ) * z)‖ ≤ 2 := norm_one_sub_exp_le_two hw
    have h3 : ‖1 - Complex.exp (-(K : ℂ) * z)‖ / ‖z‖ ≤ 2 / ‖z‖ :=
      div_le_div_of_nonneg_right h2 (le_of_lt hn)
    calc ‖F2 K z‖ = (‖1 - Complex.exp (-(K : ℂ) * z)‖ / ‖z‖) ^ 2 := by
          rw [F2, norm_pow, norm_div]
      _ ≤ (2 / ‖z‖) ^ 2 := pow_le_pow_left₀ (by positivity) h3 2
      _ = 4 / ‖z‖ ^ 2 := by rw [div_pow]; norm_num

/-- **Kernel bound (`λ ≲ 1` form).**  For `Re z ≥ 0`, `‖Hk L K z‖ ≤ e^{-(L-2K)Re z}K²`. -/
lemma norm_Hk_le_sq {L K : ℝ} (hK : 0 < K) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖Hk L K z‖ ≤ Real.exp (-(L - 2 * K) * z.re) * K ^ 2 := by
  have hexp : ‖Complex.exp (-((L - 2 * K : ℝ) : ℂ) * z)‖
      = Real.exp (-(L - 2 * K) * z.re) := by
    rw [Complex.norm_exp, Complex.mul_re]
    simp only [Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
    congr 1
    ring
  rw [Hk, norm_mul, hexp]
  exact mul_le_mul_of_nonneg_left (norm_F2_le_sq hK hz) (Real.exp_nonneg _)

/-- **Kernel bound (decaying form).**  For `Re z ≥ 0`, `‖Hk L K z‖ ≤ e^{-(L-2K)Re z}·4/‖z‖²`. -/
lemma norm_Hk_le_inv_sq {L K : ℝ} (hK : 0 < K) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖Hk L K z‖ ≤ Real.exp (-(L - 2 * K) * z.re) * (4 / ‖z‖ ^ 2) := by
  have hexp : ‖Complex.exp (-((L - 2 * K : ℝ) : ℂ) * z)‖
      = Real.exp (-(L - 2 * K) * z.re) := by
    rw [Complex.norm_exp, Complex.mul_re]
    simp only [Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
    congr 1
    ring
  rw [Hk, norm_mul, hexp]
  exact mul_le_mul_of_nonneg_left (norm_F2_le_inv_sq hK hz) (Real.exp_nonneg _)

end Work.LinnikAreas
