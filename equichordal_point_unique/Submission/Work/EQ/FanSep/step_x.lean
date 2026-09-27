import Mathlib
import Submission.Work.EQ.FanSep.Defs
import Submission.Work.EQ.SqrtNearOne
import Submission.Work.EQ.FanSep.sqrt_step
import Submission.Work.EQ.FanSep.centre_numbers

namespace Work.EQ.FanSep

open Complex
open Work.EQ

noncomputable section

/-- Real geometry of the inverse-branch estimate: if `z` is within `(1-a)/8` of a real `r` with
`|r| ≥ (1-a)/2`, then `D := (sgnR r) * z` lies in the cone `|im| ≤ re/2` of the positive real
axis, and `w` with `‖w‖ ≤ qw‖z‖`, `qw ≤ 1/2` satisfies `‖w‖ ≤ ‖D‖/2` and
`‖w/D‖ ≤ qw ≤ 1/2`. -/
theorem geom_bounds {a r qw : ℝ} {z w : ℂ} {σ : ℝ} {D : ℂ} (_ha0 : 0 < a) (ha1 : a < 1)
    (hσ : σ = sgnR r) (hD : D = (σ : ℂ) * z)
    (hr : (1 - a) / 2 ≤ |r|) (hz : ‖z - (r : ℂ)‖ ≤ (1 - a) / 8)
    (hw : ‖w‖ ≤ qw * ‖z‖) (hqw : qw ≤ 1 / 2) :
    D ≠ 0 ∧ 0 < D.re ∧ |D.im| ≤ D.re / 2 ∧ ‖w‖ ≤ ‖D‖ / 2 ∧
      (σ : ℂ) * D = z ∧ ‖w / D‖ ≤ qw ∧ ‖w / D‖ ≤ 1 / 2 := by
  have hδ : (0 : ℝ) < (1 - a) / 8 := by linarith
  have hr4 : (1 - a) / 2 = 4 * ((1 - a) / 8) := by ring
  have hr_ge : 4 * ((1 - a) / 8) ≤ |r| := by rw [← hr4]; exact hr
  have hrne : r ≠ 0 := by
    intro h; rw [h, abs_zero] at hr_ge; linarith
  have hσsq : σ * σ = 1 := by rw [hσ]; exact sgnR_sq r
  have hσabs : |σ| = 1 := by rw [hσ]; exact abs_sgnR r
  have hσr : σ * r = |r| := by rw [hσ]; exact sgnR_mul_self hrne
  have hσcases : σ = 1 ∨ σ = -1 := by rw [hσ]; exact sgnR_cases r
  -- `‖z‖ ≥ 3(1-a)/8`
  have hz_norm : 3 * ((1 - a) / 8) ≤ ‖z‖ := by
    have h1 : |r| ≤ ‖z‖ + ‖z - (r : ℂ)‖ := by
      have h := norm_sub_le z (z - (r : ℂ))
      have h2 : z - (z - (r : ℂ)) = (r : ℂ) := by ring
      rw [h2] at h
      have h3 : ‖((r : ℝ) : ℂ)‖ = |r| := RCLike.norm_ofReal r
      linarith [h, h3]
    linarith
  -- real part of `z`
  have hzre : 3 * ((1 - a) / 8) ≤ σ * z.re := by
    have h1 : σ * z.re = σ * r + σ * (z.re - r) := by ring
    have h2 : |z.re - r| ≤ ‖z - (r : ℂ)‖ := by
      have h := Complex.abs_re_le_norm (z - (r : ℂ))
      rwa [Complex.sub_re, Complex.ofReal_re] at h
    have h3 : -( |z.re - r| ) ≤ σ * (z.re - r) := by
      rcases hσcases with h | h
      · rw [h, one_mul]; exact neg_abs_le _
      · rw [h, neg_one_mul]; linarith [le_abs_self (z.re - r)]
    rw [h1, hσr]
    linarith
  have hDim : |z.im| ≤ ‖z - (r : ℂ)‖ := by
    have h := Complex.abs_im_le_norm (z - (r : ℂ))
    rwa [Complex.sub_im, Complex.ofReal_im, sub_zero] at h
  have hDre : D.re = σ * z.re := by
    rw [hD, Complex.mul_re]
    simp
  have hDim' : D.im = σ * z.im := by
    rw [hD, Complex.mul_im]
    simp
  have hDre_pos : 0 < D.re := by rw [hDre]; linarith
  have hDne : D ≠ 0 := by
    intro h
    rw [h] at hDre_pos
    simp at hDre_pos
  have hDre_ge : 3 * ((1 - a) / 8) ≤ D.re := by rw [hDre]; exact hzre
  have hDim_le : |D.im| ≤ D.re / 2 := by
    rw [hDim', abs_mul, hσabs, one_mul]
    have := hDim
    linarith [hz, hDre_ge]
  have hσD : (σ : ℂ) * D = z := by
    have hsq : (σ : ℂ) * (σ : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, hσsq, Complex.ofReal_one]
    rw [hD, ← mul_assoc, hsq, one_mul]
  have hDnorm : ‖D‖ = ‖z‖ := by
    rw [hD, norm_mul]
    have h3 : ‖((σ : ℝ) : ℂ)‖ = |σ| := RCLike.norm_ofReal σ
    rw [h3, hσabs, one_mul]
  have hw_half : ‖w‖ ≤ ‖D‖ / 2 := by
    rw [hDnorm]
    calc ‖w‖ ≤ qw * ‖z‖ := hw
      _ ≤ (1 / 2) * ‖z‖ := mul_le_mul_of_nonneg_right hqw (norm_nonneg z)
      _ = ‖z‖ / 2 := by ring
  have hwD_qw : ‖w / D‖ ≤ qw := by
    rw [norm_div]
    have hDpos : 0 < ‖D‖ := norm_pos_iff.mpr hDne
    rw [div_le_iff₀ hDpos]
    calc ‖w‖ ≤ qw * ‖z‖ := hw
      _ = qw * ‖D‖ := by rw [hDnorm]
  have hwD_half : ‖w / D‖ ≤ 1 / 2 := le_trans hwD_qw hqw
  exact ⟨hDne, hDre_pos, hDim_le, hw_half, hσD, hwD_qw, hwD_half⟩

theorem step_x {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Bool) (c : ℝ) (Q : ℂ × ℂ) (qw : ℝ),
      (1 - a) / 2 ≤ ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖ →
      ‖Q.1 - (c : ℂ)‖ ≤ (1 - a) / 8 →
      ‖Q.2‖ ≤ qw * ‖Q.1 + ((a / 2 : ℝ) : ℂ)‖ → qw ≤ 1 / 2 →
      ‖(invBranch a s Q).1 - (((-c) + sgnB s * sgnR (c + a / 2) : ℝ) : ℂ)‖ ≤
        ‖Q.1 - (c : ℂ)‖ + C * qw ^ 2 := by
  refine ⟨2, by norm_num, ?_⟩
  intro s c Q qw hca hQ1 hQ2 hqw
  set z : ℂ := Q.1 + ((a / 2 : ℝ) : ℂ) with hz
  set w : ℂ := Q.2 with hw
  set r : ℝ := c + a / 2 with hr
  set σ : ℝ := sgnR r with hσ
  set D : ℂ := (σ : ℂ) * z with hD
  have hca' : (1 - a) / 2 ≤ |r| := by
    rw [hr]
    rwa [norm_ofReal_add_eq_abs] at hca
  have hz_off : ‖z - (r : ℂ)‖ ≤ (1 - a) / 8 := by
    have he : z - (r : ℂ) = Q.1 - (c : ℂ) := by rw [hz, hr]; push_cast; ring
    rw [he]; exact hQ1
  have hw_off : ‖w‖ ≤ qw * ‖z‖ := by
    rw [hw, hz]; exact hQ2
  obtain ⟨hDne, hDre, hDim, hwD_half0, hσD, hwD_qw, hwD_half⟩ :=
    geom_bounds (a := a) (r := r) (qw := qw) (z := z) (w := w) (σ := σ) (D := D)
      ha0 ha1 hσ hD hca' hz_off hw_off hqw
  obtain ⟨-, hsqrt, hinv⟩ := sqrt_step
  -- `z ^ 2 = D ^ 2`
  have hσsq : (σ : ℂ) * (σ : ℂ) = 1 := by
    have h : σ * σ = 1 := by rw [hσ]; exact sgnR_sq r
    rw [← Complex.ofReal_mul, h, Complex.ofReal_one]
  have hzsq : z ^ 2 = D ^ 2 := by
    rw [show z = (σ : ℂ) * D from hσD.symm, mul_pow, pow_two, hσsq, one_mul]
  -- the principal-square-root factorisation
  have hρ_eq : (z ^ 2 + w ^ 2) ^ (1 / 2 : ℂ) = D * sqHalf ((w / D) ^ 2) := by
    rw [hzsq]
    exact hsqrt hDne hDre hDim hwD_half0
  have hSne : sqHalf ((w / D) ^ 2) ≠ 0 := by
    intro h
    have h1 := hinv (w / D) hwD_half
    rw [h, inv_zero, zero_sub, norm_neg, norm_one] at h1
    have h2 : ‖w / D‖ ^ 2 ≤ 1 / 4 := by nlinarith [norm_nonneg (w / D), hwD_half]
    nlinarith
  -- `z / ρ = σ * S⁻¹`
  have hzdiv : z / (z ^ 2 + w ^ 2) ^ (1 / 2 : ℂ) = (σ : ℂ) * (sqHalf ((w / D) ^ 2))⁻¹ := by
    rw [hρ_eq, show z = (σ : ℂ) * D from hσD.symm]
    field_simp
  have hdiff : z / (z ^ 2 + w ^ 2) ^ (1 / 2 : ℂ) - (σ : ℂ)
      = (σ : ℂ) * ((sqHalf ((w / D) ^ 2))⁻¹ - 1) := by
    rw [hzdiv]; ring
  -- quantitative bound
  have hS_bound : ‖(sqHalf ((w / D) ^ 2))⁻¹ - 1‖ ≤ 2 * qw ^ 2 := by
    have h1 := hinv (w / D) hwD_half
    have h2 : ‖w / D‖ ^ 2 ≤ qw ^ 2 := by nlinarith [norm_nonneg (w / D), hwD_qw]
    linarith
  have hσn : ‖(σ : ℂ)‖ = 1 := by
    have h3 : ‖((σ : ℝ) : ℂ)‖ = |σ| := RCLike.norm_ofReal σ
    rw [h3, show |σ| = 1 from by rw [hσ]; exact abs_sgnR r]
  have hzρ : ‖z / (z ^ 2 + w ^ 2) ^ (1 / 2 : ℂ) - (σ : ℂ)‖ ≤ 2 * qw ^ 2 := by
    rw [hdiff, norm_mul, hσn, one_mul]
    exact hS_bound
  -- first coordinate of the branch
  have hfst : (invBranch a s Q).1
      = -Q.1 + (sgnB s : ℂ) * (z / (z ^ 2 + w ^ 2) ^ (1 / 2 : ℂ)) := by
    have h1 : (if s then (1 : ℂ) else -1) = (sgnB s : ℂ) := by cases s <;> simp [sgnB]
    have h2 : (-Q.1 + (if s then (1 : ℂ) else -1) * (Q.1 + ((a / 2 : ℝ) : ℂ)) /
        ((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) ^ (1 / 2 : ℂ))
        = -Q.1 + (sgnB s : ℂ) * (z / (z ^ 2 + w ^ 2) ^ (1 / 2 : ℂ)) := by
      rw [← hz, ← hw, h1, mul_div_assoc]
    simpa only [invBranch] using h2
  have htarget : (((-c) + sgnB s * sgnR (c + a / 2) : ℝ) : ℂ)
      = -(c : ℂ) + (sgnB s : ℂ) * (σ : ℂ) := by
    rw [← hr, ← hσ]
    push_cast
    ring
  calc ‖(invBranch a s Q).1 - (((-c) + sgnB s * sgnR (c + a / 2) : ℝ) : ℂ)‖
      = ‖(-Q.1 + (sgnB s : ℂ) * (z / (z ^ 2 + w ^ 2) ^ (1 / 2 : ℂ)))
          - (-(c : ℂ) + (sgnB s : ℂ) * (σ : ℂ))‖ := by rw [hfst, htarget]
    _ = ‖((c : ℂ) - Q.1) + (sgnB s : ℂ) *
          (z / (z ^ 2 + w ^ 2) ^ (1 / 2 : ℂ) - (σ : ℂ))‖ := by
          congr 1; ring
    _ ≤ ‖(c : ℂ) - Q.1‖ + ‖(sgnB s : ℂ) *
          (z / (z ^ 2 + w ^ 2) ^ (1 / 2 : ℂ) - (σ : ℂ))‖ := norm_add_le _ _
    _ ≤ ‖Q.1 - (c : ℂ)‖ + 2 * qw ^ 2 := by
          have hs : ‖(sgnB s : ℂ)‖ = 1 := by
            have h3 : ‖((sgnB s : ℝ) : ℂ)‖ = |sgnB s| := RCLike.norm_ofReal (sgnB s)
            rw [h3, abs_sgnB s]
          rw [norm_mul, hs, one_mul, norm_sub_rev (c : ℂ) Q.1]
          linarith [hzρ]

end

end Work.EQ.FanSep
