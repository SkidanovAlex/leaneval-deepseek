import Mathlib
import Submission.Work.A14D.BU_defs
import Submission.Work.A14D.GZ_eval
import Submission.Work.A14D.om1_geometry

namespace Work.A14D

open Complex Metric

noncomputable section

/-- `w(z) = z/(z-1) = (|z|² − z)/‖z−1‖²` maps the half-plane `SU` into the half-plane `SL`. -/
private lemma wC_mem_SL_of_mem_SU {z : ℂ} (hz : z ∈ SU) : wC z ∈ SL := by
  have hz1 : z ≠ 1 := by
    intro h; rw [h] at hz; rw [mem_SU_iff] at hz; simp at hz
  have hN : 0 < Complex.normSq (z - 1) := by
    rw [Complex.normSq_pos]; exact sub_ne_zero.mpr hz1
  have hNval : Complex.normSq (z - 1) = (z.re - 1) ^ 2 + z.im ^ 2 := by
    rw [Complex.normSq_apply]; simp; ring
  have hre : (wC z).re = (z.re ^ 2 - z.re + z.im ^ 2) / Complex.normSq (z - 1) := by
    rw [wC, Complex.div_re,
      show (z - 1).re = z.re - 1 by simp, show (z - 1).im = z.im by simp]
    ring
  have him : (wC z).im = -z.im / Complex.normSq (z - 1) := by
    rw [wC, Complex.div_im,
      show (z - 1).re = z.re - 1 by simp, show (z - 1).im = z.im by simp]
    ring
  rw [mem_SU_iff] at hz
  rw [mem_SL_iff, him, hre]
  have hkey : -(8 : ℝ) * z.im
      < (z.re ^ 2 - z.re + z.im ^ 2) - Complex.normSq (z - 1) := by
    rw [hNval]; nlinarith [hz]
  rw [show (8 : ℝ) * (-z.im / Complex.normSq (z - 1)) + 1
      = (8 * (-z.im) + Complex.normSq (z - 1)) / Complex.normSq (z - 1) by
    field_simp]
  rw [div_lt_div_iff_of_pos_right hN]
  linarith

/-- For `‖z‖ < 39/100`, `‖w(z)‖ < 1`: indeed `‖w z‖ = ‖z‖/‖z−1‖` and `‖z−1‖ ≥ 1 − ‖z‖`. -/
private lemma norm_wC_lt_one {z : ℂ} (hz : ‖z‖ ≤ (39 : ℝ) / 100) : ‖wC z‖ < 1 := by
  have hz1 : z ≠ 1 := by
    intro h; rw [h] at hz; simp at hz; norm_num at hz
  have h1 : (1 : ℝ) - ‖z‖ ≤ ‖z - 1‖ := by
    have h := norm_sub_norm_le (1 : ℂ) z
    rw [norm_one, show (1 : ℂ) - z = -(z - 1) by ring, norm_neg] at h
    exact h
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1)
  rw [wC, norm_div, div_lt_one hpos]
  linarith

theorem Yser_GZ_eq (a b c : ℤ) (h : Submission.CDTPlan.ARel a b c) (HU HL : ℂ → ℂ)
    (hHUeq : ∀ z ∈ Work.A14D.SU ∩ Metric.ball (0 : ℂ) 1, HU z = Work.A14D.Hfun a b c z)
    (hHLeq : ∀ z ∈ Work.A14D.SL ∩ Metric.ball (0 : ℂ) 1, HL z = Work.A14D.Hfun a b c z) :
    ∀ w ∈ Work.A14D.SU ∩ Metric.ball (0 : ℂ) ((39 : ℝ) / 100),
      Work.A14D.Yser (Submission.CDTPlan.GZ a b c) w = HU w + HL (Work.A14D.wC w) := by
  intro w hw
  obtain ⟨hwSU, hwb⟩ := hw
  have hw39 : ‖w‖ ≤ (39 : ℝ) / 100 := by
    rw [Metric.mem_ball, Complex.dist_eq, sub_zero] at hwb
    exact le_of_lt hwb
  have hw1 : w ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, Complex.dist_eq, sub_zero]; linarith
  have hwc1 : wC w ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, Complex.dist_eq, sub_zero]; exact norm_wC_lt_one hw39
  rw [Yser, GZ_eval a b c h w hw39, hHUeq w ⟨hwSU, hw1⟩]
  congr 1
  exact (hHLeq (wC w) ⟨wC_mem_SL_of_mem_SU hwSU, hwc1⟩).symm

end

end Work.A14D
