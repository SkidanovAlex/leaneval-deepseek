import Mathlib
import Submission.Work.ZeroDensity.Ingham.zetaAfeDefs
import Submission.Work.ZeroDensity.Ingham.AfeProof.afeAux
import Submission.Work.ZeroDensity.Ingham.AfeProof.afeIdentity
import Submission.Work.ZeroDensity.Ingham.AfeProof.afeResonanceSumBound
import Submission.Work.ZeroDensity.Ingham.norm_zetaChi_critical

/-!
# The residual of the approximate functional equation for `ζ` at the balanced point
-/

namespace Work.ZeroDensity.Ingham.AfeProof

open MeasureTheory Set
open scoped BigOperators

noncomputable section

/-- The residual `ζ(s) - Σ_{n ≤ N} n^{-s} - χ(s)·Σ_{m ≤ M} m^{s-1}`. -/
def afeResidual (t : ℝ) : ℂ :=
  riemannZeta (cls t) - afeMain t - zetaChi (cls t) * afeDual t

lemma afeResidual_apply (t : ℝ) :
    afeResidual t = riemannZeta (cls t) - afeMain t - zetaChi (cls t) * afeDual t := rfl

lemma norm_cls_sub_one (t : ℝ) : ‖cls t - 1‖ = Real.sqrt (1 / 4 + t ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  have hre : (cls t - 1).re = -(1 / 2) := by norm_num [cls]
  have him : (cls t - 1).im = t := by simp [cls]
  rw [hre, him]
  congr 1
  ring

lemma norm_cls_le {t : ℝ} (ht : 1 ≤ t) : ‖cls t‖ ≤ 2 * t := by
  rw [norm_cls, Real.sqrt_le_iff]
  refine ⟨by linarith, ?_⟩
  nlinarith

/-- Boundedness of `ζ` on the critical segment `[1, 10⁶]`. -/
lemma exists_zeta_bound_compact :
    ∃ M : ℝ, ∀ t : ℝ, 1 ≤ t → t ≤ 1000000 → ‖riemannZeta (cls t)‖ ≤ M := by
  have hcont : ContinuousOn (fun t : ℝ => ‖riemannZeta (cls t)‖) (Set.Icc 1 (1000000:ℝ)) := by
    refine ContinuousOn.norm ?_
    intro x hx
    exact (((differentiableAt_riemannZeta (cls_ne_one x)).continuousAt).comp
      (continuous_cls.continuousAt)).continuousWithinAt
  obtain ⟨x₀, hx₀mem, hx₀max⟩ :=
    (isCompact_Icc (a := (1 : ℝ)) (b := 1000000)).exists_isMaxOn
      (Set.nonempty_Icc.mpr (by norm_num)) hcont
  exact ⟨‖riemannZeta (cls x₀)‖, fun t ht1 ht2 => hx₀max ⟨ht1, ht2⟩⟩

lemma afeResidual_bound : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t → ‖afeResidual t‖ ≤ C := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := afeResonanceSumBound
  obtain ⟨Mζ, hMζ⟩ := exists_zeta_bound_compact
  refine ⟨max (2 + 2 * C₁) (Mζ + 2 * 1000000 + 2) + 1, by positivity, ?_⟩
  intro t ht
  by_cases hsmall : t ≤ 1000000
  · -- bounded `t`: crude estimates
    have hN : (afeNt t : ℝ) ≤ 1000000 + 1 := by
      have := afeNt_le_self_add_one ht
      linarith
    have hM : (afeMt t : ℝ) ≤ 1000000 := by
      have := afeMt_le_self (by linarith : (0:ℝ) ≤ t)
      linarith
    have hchi : ‖zetaChi (cls t)‖ = 1 := norm_zetaChi_critical t
    calc ‖afeResidual t‖ = ‖riemannZeta (cls t) - afeMain t - zetaChi (cls t) * afeDual t‖ := by
          rw [afeResidual_apply]
      _ ≤ ‖riemannZeta (cls t)‖ + ‖afeMain t‖ + ‖zetaChi (cls t) * afeDual t‖ := by
          refine le_trans (norm_sub_le _ _) ?_
          exact add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ Mζ + (afeNt t : ℝ) + 1 * (afeMt t : ℝ) := by
          refine add_le_add (add_le_add (hMζ t ht hsmall) (norm_afeMain_le t)) ?_
          rw [norm_mul, hchi]
          simpa using norm_afeDual_le t
      _ ≤ Mζ + 2 * 1000000 + 2 := by linarith
      _ ≤ max (2 + 2 * C₁) (Mζ + 2 * 1000000 + 2) := le_max_right _ _
      _ ≤ max (2 + 2 * C₁) (Mζ + 2 * 1000000 + 2) + 1 := le_add_of_nonneg_right (by norm_num)
  · -- large `t`: the identity plus the resonance bound
    have hbig : (1000000:ℝ) ≤ t := le_of_lt (not_le.mp hsmall)
    have hres := hC₁ t hbig
    have hreson : zetaChi (cls t) =
        (cls t / (Real.pi : ℂ)) * (2 * (Real.pi : ℂ)) ^ (cls t) * afeC0 (cls t) :=
      afe_resonance (cls_re_pos t) (cls_re_lt_one t)
    have hkey : afeResidual t = (afeNt t : ℂ) ^ (1 - cls t) / (cls t - 1)
        - (afeNt t : ℂ) ^ (-(cls t)) / 2
        + ((cls t / (Real.pi : ℂ)) * (2 * (Real.pi : ℂ)) ^ (cls t)) *
            (afeTsum t - afeC0 (cls t) * afeDual t) := by
      rw [afeResidual_apply, afeIdentity t, hreson]
      ring
    have hb1 : ‖(afeNt t : ℂ) ^ (1 - cls t) / (cls t - 1)‖ ≤ 1 := by
      rw [norm_div]
      have hnum : ‖(afeNt t : ℂ) ^ (1 - cls t)‖ = Real.sqrt (afeNt t) := by
        rw [← Complex.ofReal_natCast,
          Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast one_le_afeNt t)]
        have h1 : (1 - cls t).re = 1 / 2 := by norm_num [cls]
        rw [h1, ← Real.sqrt_eq_rpow]
      rw [hnum, norm_cls_sub_one]
      rw [div_le_one (Real.sqrt_pos.mpr (by positivity))]
      apply Real.sqrt_le_sqrt
      have hN := afeNt_le_self_add_one ht
      nlinarith
    have hb2 : ‖(afeNt t : ℂ) ^ (-(cls t)) / 2‖ ≤ 1 / 2 := by
      rw [norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
      have hnum : ‖(afeNt t : ℂ) ^ (-(cls t))‖ = (Real.sqrt (afeNt t))⁻¹ := by
        rw [← Complex.ofReal_natCast,
          Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast one_le_afeNt t)]
        have h1 : (-(cls t)).re = -(1 / 2) := by norm_num [cls]
        have hNpos : (0:ℝ) < (afeNt t : ℝ) :=
          lt_of_lt_of_le zero_lt_one (by exact_mod_cast one_le_afeNt t)
        rw [h1, Real.rpow_neg (le_of_lt hNpos) (1/2), ← Real.sqrt_eq_rpow]
      rw [hnum, show (1:ℝ)/2 * 2 = 1 by norm_num]
      exact inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr (by exact_mod_cast one_le_afeNt t))
    have hG : ‖(cls t / (Real.pi : ℂ)) * (2 * (Real.pi : ℂ)) ^ (cls t)‖ ≤ 2 * t := by
      rw [norm_afeGauge]
      have h1 := norm_cls_le (by linarith : (1:ℝ) ≤ t)
      have h2 : Real.sqrt (2 * Real.pi) / Real.pi ≤ 1 := by
        have hπ : (0:ℝ) < Real.pi := Real.pi_pos
        have hsq := Real.sq_sqrt (show (0:ℝ) ≤ 2 * Real.pi by positivity)
        have hsp : (0:ℝ) ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
        rw [div_le_one hπ]
        nlinarith [Real.pi_gt_three]
      calc ‖cls t‖ * Real.sqrt (2 * Real.pi) / Real.pi
          = ‖cls t‖ * (Real.sqrt (2 * Real.pi) / Real.pi) := by ring
        _ ≤ (2 * t) * 1 := mul_le_mul h1 h2 (by positivity) (by linarith)
        _ = 2 * t := by ring
    have h2C : (2 * t) * (C₁ / t) = 2 * C₁ := by
      have ht0 : (0:ℝ) < t := by linarith
      rw [show (2 * t) * (C₁ / t) = (2 * t * C₁) / t by ring,
        show (2 * t * C₁) = t * (2 * C₁) by ring]
      exact mul_div_cancel_left₀ (2 * C₁) (ne_of_gt ht0)
    calc ‖afeResidual t‖
        = ‖(afeNt t : ℂ) ^ (1 - cls t) / (cls t - 1) - (afeNt t : ℂ) ^ (-(cls t)) / 2
            + ((cls t / (Real.pi : ℂ)) * (2 * (Real.pi : ℂ)) ^ (cls t)) *
                (afeTsum t - afeC0 (cls t) * afeDual t)‖ := by rw [hkey]
      _ ≤ ‖(afeNt t : ℂ) ^ (1 - cls t) / (cls t - 1) - (afeNt t : ℂ) ^ (-(cls t)) / 2‖
            + ‖((cls t / (Real.pi : ℂ)) * (2 * (Real.pi : ℂ)) ^ (cls t)) *
                (afeTsum t - afeC0 (cls t) * afeDual t)‖ := norm_add_le _ _
      _ ≤ (‖(afeNt t : ℂ) ^ (1 - cls t) / (cls t - 1)‖ + ‖(afeNt t : ℂ) ^ (-(cls t)) / 2‖)
            + ‖(cls t / (Real.pi : ℂ)) * (2 * (Real.pi : ℂ)) ^ (cls t)‖ *
                ‖afeTsum t - afeC0 (cls t) * afeDual t‖ := by
          rw [norm_mul]
          exact add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ (1 + 1 / 2) + (2 * t) * (C₁ / t) :=
          add_le_add (add_le_add hb1 hb2)
            (mul_le_mul hG hres (norm_nonneg _) (by positivity))
      _ = (3 / 2 + 2 * C₁) := by rw [h2C]; ring
      _ ≤ max (2 + 2 * C₁) (Mζ + 2 * 1000000 + 2) := le_trans (by linarith) (le_max_left _ _)
      _ ≤ max (2 + 2 * C₁) (Mζ + 2 * 1000000 + 2) + 1 := le_add_of_nonneg_right (by norm_num)

end

end Work.ZeroDensity.Ingham.AfeProof
