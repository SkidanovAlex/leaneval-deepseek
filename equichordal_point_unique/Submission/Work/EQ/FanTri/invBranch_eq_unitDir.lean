import Mathlib
import Submission.Work.EQ.FanSep.sqrt_step
import Submission.Work.EQ.FanSep.step_x
import Submission.Work.EQ.FanTri.invBranchDefs

namespace Work.EQ.FanTri

open Complex

/-- Consequence of `FanSep.sqrt_step`: on the cone `|im| ≤ re/2` where `D` dominates `Y`, the
principal square root factors out of the fraction. -/
private lemma div_sqrt_eq_inv_sqHalf_aux {D Y : ℂ} (hD : D ≠ 0) (hre : 0 < D.re)
    (him : |D.im| ≤ D.re / 2) (hY : ‖Y‖ ≤ ‖D‖ / 2) :
    D / (D ^ 2 + Y ^ 2) ^ (1 / 2 : ℂ) = (sqHalf ((Y / D) ^ 2))⁻¹ := by
  obtain ⟨-, hsqrt, hinv⟩ := FanSep.sqrt_step
  have hwD_half : ‖Y / D‖ ≤ 1 / 2 := by
    rw [norm_div]
    have hDpos : 0 < ‖D‖ := norm_pos_iff.mpr hD
    rw [div_le_iff₀ hDpos]
    linarith [hY]
  have hSne : sqHalf ((Y / D) ^ 2) ≠ 0 := by
    intro h
    have h1 := hinv (Y / D) hwD_half
    rw [h, inv_zero, zero_sub, norm_neg, norm_one] at h1
    have h2 : ‖Y / D‖ ^ 2 ≤ 1 / 4 := by nlinarith [norm_nonneg (Y / D), hwD_half]
    nlinarith
  have hp : (D ^ 2 + Y ^ 2) ^ (1 / 2 : ℂ) = D * sqHalf ((Y / D) ^ 2) := hsqrt hD hre him hY
  rw [hp]
  field_simp

theorem invBranch_eq_unitDir {a c : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hc : (1 - a) / 2 ≤ ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖) (s : Bool) {Q : ℂ × ℂ}
    (hQ : ‖Q - ((c : ℂ), (0 : ℂ))‖ ≤ (1 - a) / 8) :
    invBranch a s Q =
      (-Q.1 + ((if s then (1 : ℂ) else -1) * ((sgnR (c + a / 2) : ℝ) : ℂ)) *
          (unitDir (Q.2 / (Q.1 + ((a / 2 : ℝ) : ℂ)))).1,
       -Q.2 + ((if s then (1 : ℂ) else -1) * ((sgnR (c + a / 2) : ℝ) : ℂ)) *
          (unitDir (Q.2 / (Q.1 + ((a / 2 : ℝ) : ℂ)))).2) := by
  set z : ℂ := Q.1 + ((a / 2 : ℝ) : ℂ) with hz
  set w : ℂ := Q.2 with hw
  set r : ℝ := c + a / 2 with hr
  set σ : ℝ := sgnR r with hσ
  set D : ℂ := (σ : ℂ) * z with hD
  have hca' : (1 - a) / 2 ≤ |r| := by
    rw [hr]
    rwa [FanSep.norm_ofReal_add_eq_abs] at hc
  have hz_off : ‖z - (r : ℂ)‖ ≤ (1 - a) / 8 := by
    have he : z - (r : ℂ) = Q.1 - (c : ℂ) := by rw [hz, hr]; push_cast; ring
    rw [he]
    calc ‖Q.1 - (c : ℂ)‖ ≤ ‖Q - ((c : ℂ), (0 : ℂ))‖ := by
          simpa using norm_fst_le (Q - ((c : ℂ), (0 : ℂ)))
      _ ≤ (1 - a) / 8 := hQ
  have hz_norm : 3 * ((1 - a) / 8) ≤ ‖z‖ := by
    have h1 : |r| ≤ ‖z‖ + ‖z - (r : ℂ)‖ := by
      have h := norm_sub_le z (z - (r : ℂ))
      have h2 : z - (z - (r : ℂ)) = (r : ℂ) := by ring
      rw [h2] at h
      have h3 : ‖((r : ℝ) : ℂ)‖ = |r| := RCLike.norm_ofReal r
      linarith [h, h3]
    linarith
  have hw_off : ‖w‖ ≤ (1 / 3) * ‖z‖ := by
    have hQ2 : ‖Q.2‖ ≤ (1 - a) / 8 := by
      simpa using le_trans (norm_snd_le (Q - ((c : ℂ), (0 : ℂ)))) hQ
    have h3 : (1 / 3) * (3 * ((1 - a) / 8)) ≤ (1 / 3) * ‖z‖ :=
      mul_le_mul_of_nonneg_left hz_norm (by norm_num)
    rw [hw]
    linarith
  obtain ⟨hDne, hDre, hDim, hwD, hσD, -, -⟩ :=
    FanSep.geom_bounds (a := a) (r := r) (qw := 1 / 3) (z := z) (w := w) (σ := σ) (D := D)
      ha0 ha1 rfl rfl hca' hz_off hw_off (by norm_num)
  have hmulne : (σ : ℂ) * z ≠ 0 := by rw [← hD]; exact hDne
  have hzne : z ≠ 0 := right_ne_zero_of_mul hmulne
  have hσsq : (σ : ℂ) * (σ : ℂ) = 1 := by
    rw [← Complex.ofReal_mul]
    rw [show σ * σ = 1 from by rw [hσ]; exact sgnR_sq r, Complex.ofReal_one]
  have hdiv := div_sqrt_eq_inv_sqHalf_aux (D := D) (Y := w) hDne hDre hDim hwD
  have hzsq : z ^ 2 = D ^ 2 := by
    rw [show z = (σ : ℂ) * D from hσD.symm, mul_pow, pow_two, hσsq, one_mul]
  have hwD_eq : (w / D) ^ 2 = (w / z) ^ 2 := by
    rw [div_pow, div_pow, hzsq]
  have hz_div : z / (z ^ 2 + w ^ 2) ^ (1 / 2 : ℂ)
      = (σ : ℂ) * (sqHalf ((w / z) ^ 2))⁻¹ := by
    have h1 : z / (z ^ 2 + w ^ 2) ^ (1 / 2 : ℂ)
        = (σ : ℂ) * (D / (D ^ 2 + w ^ 2) ^ (1 / 2 : ℂ)) := by
      rw [hzsq, show z = (σ : ℂ) * D from hσD.symm, mul_div_assoc]
    rw [h1, hdiv, hwD_eq]
  have hw_div : w / (z ^ 2 + w ^ 2) ^ (1 / 2 : ℂ)
      = (σ : ℂ) * (w / z) * (sqHalf ((w / z) ^ 2))⁻¹ := by
    have hfact : w / (z ^ 2 + w ^ 2) ^ (1 / 2 : ℂ)
        = (w / z) * (z / (z ^ 2 + w ^ 2) ^ (1 / 2 : ℂ)) := by
      rw [← mul_div_assoc, div_mul_cancel₀ w hzne]
    rw [hfact, hz_div]
    ring
  unfold invBranch
  simp only [unitDir_fst, unitDir_snd]
  rw [← hz, ← hw]
  simp only [mul_div_assoc]
  rw [hz_div, hw_div]
  refine Prod.ext ?_ ?_ <;> ring

end Work.EQ.FanTri
