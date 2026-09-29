import Mathlib
import Submission.Work.TMComp.RedProj.integral_shift_eq_of_periodic_strip
import Submission.Work.TMComp.RedProj.fourierCoeffOn_eq_exp_integral
import Submission.Work.TMComp.RedProj.norm_integral_shift_le

open scoped Interval
open MeasureTheory

namespace Work.TMComp.RedProj

theorem fourierCoeff_decay_of_strip (φ : ℝ → ℂ) (Φ : ℂ → ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hΦ : DifferentiableOn ℂ Φ {w : ℂ | |w.im| < ρ})
    (hper : ∀ w : ℂ, |w.im| < ρ → Φ (w + 1) = Φ w)
    (hφ : ∀ x : ℝ, Φ (x : ℂ) = φ x) :
    ∃ C η : ℝ, 0 < η ∧ ∀ k : ℤ,
      ‖fourierCoeffOn (show (0:ℝ) < 1 by norm_num) φ k‖ ≤ C * Real.exp (-(η * |(k : ℝ)|)) := by
  set σ : ℝ := ρ / 2 with hσ
  have hσpos : 0 < σ := by rw [hσ]; linarith
  have hσlt : σ < ρ := by rw [hσ]; linarith
  have hσabs : |σ| < ρ := by rw [abs_of_pos hσpos]; exact hσlt
  have hmσabs : |-σ| < ρ := by rw [abs_neg, abs_of_pos hσpos]; exact hσlt
  set Cp : ℝ := ∫ x in (0:ℝ)..1, ‖Φ ((x : ℂ) + (σ : ℂ) * Complex.I)‖ with hCp
  set Cm : ℝ := ∫ x in (0:ℝ)..1, ‖Φ ((x : ℂ) + ((-σ : ℝ) : ℂ) * Complex.I)‖ with hCm
  have hCpnn : 0 ≤ Cp := by
    rw [hCp]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun u _ => norm_nonneg _)
  have hCmnn : 0 ≤ Cm := by
    rw [hCm]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun u _ => norm_nonneg _)
  have hηpos : 0 < 2 * Real.pi * σ := by
    have h2π : (0:ℝ) < 2 * Real.pi := by positivity
    exact mul_pos h2π hσpos
  have hbridge : ∀ k : ℤ, fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) φ k =
      ∫ x in (0 : ℝ)..1, Φ (x : ℂ) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (x : ℂ))) := by
    intro k
    rw [fourierCoeffOn_eq_exp_integral]
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [hφ x]
  refine ⟨Cp + Cm + 1, 2 * Real.pi * σ, hηpos, fun k => ?_⟩
  have hCple : Cp ≤ Cp + Cm + 1 := by linarith
  have hCmle : Cm ≤ Cp + Cm + 1 := by linarith
  rcases lt_or_ge (0 : ℤ) k with hk | hk
  · have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    calc ‖fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) φ k‖
        = ‖∫ x in (0 : ℝ)..1, Φ (x : ℂ) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (x : ℂ)))‖ := by
            rw [hbridge k]
      _ = ‖∫ x in (0 : ℝ)..1, Φ ((x : ℂ) + ((-σ : ℝ) : ℂ) * Complex.I) *
              Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((x : ℂ) + ((-σ : ℝ) : ℂ) * Complex.I)))‖ := by
            rw [integral_shift_eq_of_periodic_strip Φ ρ hρ hΦ hper k (-σ) hmσabs]
      _ ≤ Cm * Real.exp (2 * Real.pi * (k : ℝ) * (-σ)) := by
            simpa [hCm] using norm_integral_shift_le Φ (-σ) k
      _ ≤ (Cp + Cm + 1) * Real.exp (-((2 * Real.pi * σ) * |(k : ℝ)|)) := by
            have hexp : Real.exp (2 * Real.pi * (k : ℝ) * (-σ)) =
                Real.exp (-((2 * Real.pi * σ) * |(k : ℝ)|)) := by
              congr 1
              rw [abs_of_pos hkpos]
              ring
            rw [hexp]
            exact mul_le_mul_of_nonneg_right hCmle (Real.exp_pos _).le
  · have hknp : (k : ℝ) ≤ 0 := by exact_mod_cast hk
    calc ‖fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) φ k‖
        = ‖∫ x in (0 : ℝ)..1, Φ (x : ℂ) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (x : ℂ)))‖ := by
            rw [hbridge k]
      _ = ‖∫ x in (0 : ℝ)..1, Φ ((x : ℂ) + (σ : ℂ) * Complex.I) *
              Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((x : ℂ) + (σ : ℂ) * Complex.I)))‖ := by
            rw [integral_shift_eq_of_periodic_strip Φ ρ hρ hΦ hper k σ hσabs]
      _ ≤ Cp * Real.exp (2 * Real.pi * (k : ℝ) * σ) := by
            simpa [hCp] using norm_integral_shift_le Φ σ k
      _ ≤ (Cp + Cm + 1) * Real.exp (-((2 * Real.pi * σ) * |(k : ℝ)|)) := by
            have hexp : Real.exp (2 * Real.pi * (k : ℝ) * σ) =
                Real.exp (-((2 * Real.pi * σ) * |(k : ℝ)|)) := by
              congr 1
              rw [abs_of_nonpos hknp]
              ring
            rw [hexp]
            exact mul_le_mul_of_nonneg_right hCple (Real.exp_pos _).le

end Work.TMComp.RedProj
