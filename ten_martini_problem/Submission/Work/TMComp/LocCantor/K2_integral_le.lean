import Mathlib
import Submission.Work.TMComp.Kotani.ell_defect_le
import Submission.Work.TMComp.Kotani.inv_N_le
import Submission.Work.TMComp.Kotani.hasDerivAt_ell
import Submission.Work.TMComp.Kotani.Objects

namespace Work.TMComp.LocCantor

open MeasureTheory Work.TMComp.Kotani

theorem K2_integral_le (α lam : ℝ) (E₀ ε : ℝ) (hε : 0 < ε) :
    ∫ y in (0 : ℝ)..1,
        (1 / Work.TMComp.Kotani.N1 α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) y
          + 1 / Work.TMComp.Kotani.N2 α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) y
          - 4 * (-1 / Work.TMComp.Kotani.defect α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) y).im)
      ≤ 4 * (Work.TMComp.Kotani.ell α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) / ε
          - ∫ y in (0 : ℝ)..1,
              (-1 / Work.TMComp.Kotani.defect α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) y).im) := by
  set E : ℂ := (E₀ : ℂ) + (ε : ℂ) * Complex.I with hEdef
  have hEim : E.im = ε := by rw [hEdef]; simp
  have hE : 0 < E.im := hEim ▸ hε
  have hf1cont : Continuous (fun y : ℝ => 1 / N1 α lam E y) :=
    continuous_const.div (N1_cont α lam E hE) (fun y => ne_of_gt (N1_pos α lam E hE y))
  have hf2cont : Continuous (fun y : ℝ => 1 / N2 α lam E y) :=
    continuous_const.div (N2_cont α lam E hE) (fun y => ne_of_gt (N2_pos α lam E hE y))
  have hgcont : Continuous (fun y : ℝ => (-1 / defect α lam E y).im) :=
    Complex.continuous_im.comp
      (continuous_const.div (continuous_defect_phase α lam hE)
        (fun y => defect_ne_zero α lam hE y))
  have hf1 : IntervalIntegrable (fun y : ℝ => 1 / N1 α lam E y) volume 0 1 :=
    hf1cont.intervalIntegrable 0 1
  have hf2 : IntervalIntegrable (fun y : ℝ => 1 / N2 α lam E y) volume 0 1 :=
    hf2cont.intervalIntegrable 0 1
  have hg : IntervalIntegrable (fun y : ℝ => (-1 / defect α lam E y).im) volume 0 1 :=
    hgcont.intervalIntegrable 0 1
  have h45 : IntervalIntegrable (fun y : ℝ => (4 : ℝ) * (-1 / defect α lam E y).im) volume 0 1 :=
    (continuous_const.mul hgcont).intervalIntegrable 0 1
  have hsplit : (∫ y in (0 : ℝ)..1,
        (1 / N1 α lam E y + 1 / N2 α lam E y - 4 * (-1 / defect α lam E y).im))
      = (∫ y in (0 : ℝ)..1, 1 / N1 α lam E y) + (∫ y in (0 : ℝ)..1, 1 / N2 α lam E y)
        - 4 * (∫ y in (0 : ℝ)..1, (-1 / defect α lam E y).im) := by
    rw [intervalIntegral.integral_sub (hf1.add hf2) h45,
        intervalIntegral.integral_add hf1 hf2,
        intervalIntegral.integral_const_mul]
  rw [hsplit]
  obtain ⟨hI1, hI2⟩ := inv_N_le α lam E hE
  have hI1' : (∫ y in (0 : ℝ)..1, 1 / N1 α lam E y) ≤ 2 * ell α lam E / ε := by
    rw [hEim] at hI1; exact hI1
  have hI2' : (∫ y in (0 : ℝ)..1, 1 / N2 α lam E y) ≤ 2 * ell α lam E / ε := by
    rw [hEim] at hI2; exact hI2
  have hL : (4 : ℝ) * (ell α lam E / ε) = (2 * ell α lam E / ε) + (2 * ell α lam E / ε) := by
    ring
  linarith [hI1', hI2', hL]

end Work.TMComp.LocCantor
