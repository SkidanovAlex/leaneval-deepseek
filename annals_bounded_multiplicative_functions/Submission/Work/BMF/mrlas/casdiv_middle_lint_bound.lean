import Mathlib
import Submission.Work.BMF.window_weighted_integral_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory intervalIntegral
open scoped ENNReal

namespace Work.BMF.mrlas

theorem casdiv_middle_lint_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : ℝ → ℝ), Continuous F → (∀ τ, 0 ≤ F τ) →
      ∀ B a T : ℝ, 1 ≤ a → 1 ≤ T → (∀ c : ℝ, (∫ τ in c..(c+1), F τ) ≤ B) →
        (∫⁻ τ in Set.Icc (-T) T, ENNReal.ofReal (F τ / (a ^ 2 + τ ^ 2)))
          ≤ ENNReal.ofReal (C * B) := by
  obtain ⟨C, hCpos, hC⟩ := Work.BMF.window_weighted_integral_bound
  refine ⟨C, hCpos, ?_⟩
  intro F hFc hFnn B a T ha hT hwin
  set g : ℝ → ℝ := fun τ => F τ / (a ^ 2 + τ ^ 2) with hgdef
  have hden : ∀ τ : ℝ, 0 < a ^ 2 + τ ^ 2 := fun τ => by nlinarith [ha, sq_nonneg τ]
  have hgnn : ∀ τ, 0 ≤ g τ := fun τ => div_nonneg (hFnn τ) (le_of_lt (hden τ))
  have hgc : Continuous g := hFc.div (by continuity) (fun τ => ne_of_gt (hden τ))
  have hreal : (∫ τ in (-T)..T, g τ) ≤ C * B := by
    rw [hgdef]; exact hC F hFc hFnn B a T ha hT hwin
  have hTle : -T ≤ T := by linarith
  have hIoc : (∫ τ in Set.Ioc (-T) T, g τ) = ∫ τ in (-T)..T, g τ :=
     (intervalIntegral.integral_of_le hTle).symm
  have hIcc : (∫ τ in Set.Icc (-T) T, g τ) = ∫ τ in Set.Ioc (-T) T, g τ :=
    (setIntegral_congr_set Ioc_ae_eq_Icc).symm
  have hfi : Integrable g (volume.restrict (Set.Icc (-T) T)) :=
    hgc.continuousOn.integrableOn_compact isCompact_Icc
  have hkey := (ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ hgnn)).symm
  have hfin : (∫ τ in Set.Icc (-T) T, g τ) ≤ C * B := by
    rw [hIcc, hIoc]; exact hreal
  rw [hkey]
  exact ENNReal.ofReal_le_ofReal hfin

end Work.BMF.mrlas
