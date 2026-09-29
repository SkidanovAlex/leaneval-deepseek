import Mathlib
import Submission.Work.TMComp.Kotani.Objects
import Submission.Work.TMComp.Kotani.inv_N_le
import Submission.Work.TMComp.Kotani.L6_algebra
import Submission.Work.TMComp.Kotani.mfun_im_shift
import Submission.Work.TMComp.Kotani.EllDerivDefs
import Submission.Work.TMComp.Kotani.Psi_bounds

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMComp.Kotani

open Work.TMContract

/-! ## Positivity and continuity of `N₁`, `N₂` -/

theorem N1_pos (α lam : ℝ) (E : ℂ) (hE : 0 < E.im) (y : ℝ) : 0 < N1 α lam E y := by
  rw [N1]
  have := mfun_im_ge_self α lam hE y
  linarith

theorem N2_pos (α lam : ℝ) (E : ℂ) (hE : 0 < E.im) (y : ℝ) : 0 < N2 α lam E y := by
  rw [N2]
  have := sigSec_im_pos α lam hE y
  linarith

theorem N1_cont (α lam : ℝ) (E : ℂ) (hE : 0 < E.im) :
    Continuous (fun y : ℝ => N1 α lam E y) := by
  have h2 : Continuous (fun y : ℝ => (mfun α lam E y).im) :=
    Complex.continuous_im.comp (continuous_mfun_phase α lam hE)
  have h3 : Continuous (fun y : ℝ => (mfun α lam E y).im - E.im / 2) :=
    h2.sub continuous_const
  exact h3.congr (fun y => by rw [N1])

theorem N2_cont (α lam : ℝ) (E : ℂ) (hE : 0 < E.im) :
    Continuous (fun y : ℝ => N2 α lam E y) := by
  have hsig : Continuous (fun y : ℝ => sigSec α lam E y) := by
    have h1 : Continuous (fun y : ℝ => mfun α lam E (α - y)) :=
      (continuous_mfun_phase α lam hE).comp (continuous_const.sub continuous_id)
    have h2 : Continuous (fun y : ℝ => star (mfun α lam E (α - y))) := continuous_star.comp h1
    have h2n : ∀ y, star (mfun α lam E (α - y)) ≠ 0 := fun y => by
      rw [star_ne_zero]
      exact ne_of_apply_ne Complex.im (ne_of_gt (MfunProbs.mfun_im_pos α lam hE (α - y)))
    have h3 : Continuous (fun y : ℝ => (1 : ℂ) / star (mfun α lam E (α - y))) :=
      continuous_const.div h2 h2n
    exact h3.congr (fun y => by rw [sigSec])
  have h4 : Continuous (fun y : ℝ => (sigSec α lam E y).im) := Complex.continuous_im.comp hsig
  have h5 : Continuous (fun y : ℝ => (sigSec α lam E y).im + E.im / 2) :=
    h4.add continuous_const
  exact h5.congr (fun y => by rw [N2])

/-! ## The pointwise bound from (L6) -/

theorem defect_inv_im_le (α lam : ℝ) (E : ℂ) (hE : 0 < E.im) (y : ℝ) :
    (-1 / defect α lam E y).im ≤ (1 / 4) * (1 / N1 α lam E y + 1 / N2 α lam E y) := by
  have hN1 : 0 < N1 α lam E y := N1_pos α lam E hE y
  have hN2 : 0 < N2 α lam E y := N2_pos α lam E hE y
  set r : ℂ := ((E.im / 2 : ℝ) : ℂ) * Complex.I with hr
  set a : ℂ := mfun α lam E y - r with ha
  set c : ℂ := sigSec α lam E y + r with hc
  have haim : a.im = N1 α lam E y := by
    rw [ha, hr, N1]
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, add_zero, mul_one]
  have hcim : c.im = N2 α lam E y := by
    rw [hc, hr, N2]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, add_zero, mul_one]
  have hr_star : star r = -r := by
    rw [hr]
    simp only [star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hdef : a - star c = defect α lam E y := by
    rw [ha, hc, star_add, hr_star]
    rw [defect]
    rw [← conj_sigSec]
    ring
  have hL6 := L6_algebra a c (by rw [haim]; exact hN1) (by rw [hcim]; exact hN2)
  rw [haim, hcim, hdef] at hL6
  have hRHS : 0 ≤ (defect α lam E y).im * ‖a - c‖ ^ 2
      / (N1 α lam E y * N2 α lam E y * ‖defect α lam E y‖ ^ 2) := by
    apply div_nonneg
    · exact mul_nonneg (le_of_lt (defect_im_pos α lam hE y)) (sq_nonneg _)
    · positivity
  have hge : 0 ≤ 1 / N1 α lam E y + 1 / N2 α lam E y - 4 * (-1 / defect α lam E y).im := by
    rw [hL6]; exact hRHS
  linarith

/-! ## The integral bound -/

theorem ell_defect_le (α lam : ℝ) (E : ℂ) (hE : 0 < E.im) :
    (∫ y in (0 : ℝ)..1, (-1 / Work.TMComp.Kotani.defect α lam E y).im)
      ≤ Work.TMComp.Kotani.ell α lam E / E.im := by
  have hcont_def : Continuous (fun y : ℝ => defect α lam E y) := continuous_defect_phase α lam hE
  have hdef_ne : ∀ y : ℝ, defect α lam E y ≠ 0 := fun y => defect_ne_zero α lam hE y
  have hf_cont : Continuous (fun y : ℝ => (-1 / defect α lam E y).im) :=
    Complex.continuous_im.comp (continuous_const.div hcont_def hdef_ne)
  have hcont_N1 : Continuous (fun y : ℝ => N1 α lam E y) := N1_cont α lam E hE
  have hcont_N2 : Continuous (fun y : ℝ => N2 α lam E y) := N2_cont α lam E hE
  have hN1pos : ∀ y : ℝ, 0 < N1 α lam E y := fun y => N1_pos α lam E hE y
  have hN2pos : ∀ y : ℝ, 0 < N2 α lam E y := fun y => N2_pos α lam E hE y
  have hinvN1 : Continuous (fun y : ℝ => 1 / N1 α lam E y) :=
    continuous_const.div hcont_N1 (fun y => ne_of_gt (hN1pos y))
  have hinvN2 : Continuous (fun y : ℝ => 1 / N2 α lam E y) :=
    continuous_const.div hcont_N2 (fun y => ne_of_gt (hN2pos y))
  have hg_cont : Continuous (fun y : ℝ => (1 / 4) * (1 / N1 α lam E y + 1 / N2 α lam E y)) :=
    continuous_const.mul (hinvN1.add hinvN2)
  have hmono : (∫ y in (0 : ℝ)..1, (-1 / defect α lam E y).im)
      ≤ ∫ y in (0 : ℝ)..1, (1 / 4) * (1 / N1 α lam E y + 1 / N2 α lam E y) := by
    apply intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1) zero_le_one
      (hf_cont.intervalIntegrable 0 1) (hg_cont.intervalIntegrable 0 1)
    intro y _
    exact defect_inv_im_le α lam E hE y
  have h1int : IntervalIntegrable (fun y : ℝ => 1 / N1 α lam E y) volume (0 : ℝ) 1 :=
    hinvN1.intervalIntegrable _ _
  have h2int : IntervalIntegrable (fun y : ℝ => 1 / N2 α lam E y) volume (0 : ℝ) 1 :=
    hinvN2.intervalIntegrable _ _
  have hsplit : (∫ y in (0 : ℝ)..1, (1 / 4) * (1 / N1 α lam E y + 1 / N2 α lam E y))
      = (1 / 4) * ((∫ y in (0 : ℝ)..1, 1 / N1 α lam E y)
          + (∫ y in (0 : ℝ)..1, 1 / N2 α lam E y)) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add h1int h2int]
  have hInv := inv_N_le α lam E hE
  calc (∫ y in (0 : ℝ)..1, (-1 / Work.TMComp.Kotani.defect α lam E y).im)
      ≤ ∫ y in (0 : ℝ)..1, (1 / 4) * (1 / N1 α lam E y + 1 / N2 α lam E y) := hmono
    _ = (1 / 4) * ((∫ y in (0 : ℝ)..1, 1 / N1 α lam E y)
          + (∫ y in (0 : ℝ)..1, 1 / N2 α lam E y)) := hsplit
    _ ≤ (1 / 4) * (2 * ell α lam E / E.im + 2 * ell α lam E / E.im) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        linarith [hInv.1, hInv.2]
    _ = ell α lam E / E.im := by ring

end Work.TMComp.Kotani
