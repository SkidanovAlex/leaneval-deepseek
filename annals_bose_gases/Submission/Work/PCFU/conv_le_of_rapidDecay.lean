import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.PCFU

theorem conv_le_of_rapidDecay {χ : EuclideanSpace ℝ (Fin 3) → ℝ}
    {f : EuclideanSpace ℝ (Fin 3) → ℂ} (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    (hfm : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume)
    (hf : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : EuclideanSpace ℝ (Fin 3), ‖f x‖ ≤ C * (1 + ‖x‖) ^ (-(n : ℤ))) :
    ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ u : EuclideanSpace ℝ (Fin 3),
      ‖∫ x : EuclideanSpace ℝ (Fin 3), (χ x : ℂ) * f (u - x)‖
        ≤ C * (1 + ‖u‖) ^ (-(n : ℤ)) := by
  have _ := hfm
  intro n
  obtain ⟨Cn, hCn0, hfCn⟩ := hf n
  -- χ is supported in a ball of radius `R`
  obtain ⟨R, hRpos, hR⟩ : ∃ R > 0, ∀ x ∈ tsupport χ, ‖x‖ ≤ R :=
    hχs.isCompact.isBounded.exists_pos_norm_le
  have hχint : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) => χ x)
      MeasureTheory.volume := hχc.integrable_of_hasCompactSupport hχs
  have hχint' : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) => ‖χ x‖)
      MeasureTheory.volume := hχint.norm
  refine ⟨Cn * (1 + R) ^ n * ∫ x : EuclideanSpace ℝ (Fin 3), ‖χ x‖, ?_, ?_⟩
  · have hI : 0 ≤ ∫ x : EuclideanSpace ℝ (Fin 3), ‖χ x‖ :=
      MeasureTheory.integral_nonneg (fun x => norm_nonneg _)
    positivity
  · intro u
    set c : ℝ := Cn * (1 + R) ^ n * (1 + ‖u‖) ^ (-(n : ℤ)) with hc
    have hbound : ∀ x : EuclideanSpace ℝ (Fin 3), ‖(χ x : ℂ) * f (u - x)‖ ≤ ‖χ x‖ * c := by
      intro x
      rw [norm_mul, Complex.norm_real]
      by_cases hx : χ x = 0
      · simp [hx]
      · have hsupp : ‖x‖ ≤ R := hR x (subset_tsupport χ (Function.mem_support.mpr hx))
        have h1 : 1 + ‖u‖ ≤ (1 + R) * (1 + ‖u - x‖) := by
          have hu : ‖u‖ ≤ ‖u - x‖ + ‖x‖ := by
            have h : (u - x) + x = u := by abel
            calc ‖u‖ = ‖(u - x) + x‖ := by rw [h]
              _ ≤ ‖u - x‖ + ‖x‖ := norm_add_le _ _
          nlinarith [hsupp, hRpos.le, norm_nonneg (u - x),
            mul_nonneg hRpos.le (norm_nonneg (u - x))]
        have hzpow : (1 + ‖u - x‖) ^ (-(n : ℤ)) ≤ (1 + R) ^ n * (1 + ‖u‖) ^ (-(n : ℤ)) := by
          have hp : (0 : ℝ) < (1 + ‖u‖) ^ n := by positivity
          have hq : (0 : ℝ) < (1 + ‖u - x‖) ^ n := by positivity
          rw [zpow_neg, zpow_natCast, zpow_neg, zpow_natCast]
          rw [le_mul_inv_iff₀ hp, inv_mul_eq_div, div_le_iff₀ hq, ← mul_pow]
          exact pow_le_pow_left₀ (by positivity) h1 n
        calc ‖χ x‖ * ‖f (u - x)‖ ≤ ‖χ x‖ * (Cn * (1 + ‖u - x‖) ^ (-(n : ℤ))) :=
              mul_le_mul_of_nonneg_left (hfCn (u - x)) (norm_nonneg _)
          _ ≤ ‖χ x‖ * (Cn * ((1 + R) ^ n * (1 + ‖u‖) ^ (-(n : ℤ)))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hzpow hCn0) (norm_nonneg _)
          _ = ‖χ x‖ * c := by rw [hc]; ring
    have hgint : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) => ‖χ x‖ * c)
        MeasureTheory.volume := hχint'.mul_const c
    have hmain := MeasureTheory.norm_integral_le_of_norm_le hgint
      (Filter.Eventually.of_forall hbound)
    calc ‖∫ x : EuclideanSpace ℝ (Fin 3), (χ x : ℂ) * f (u - x)‖
        ≤ ∫ x : EuclideanSpace ℝ (Fin 3), ‖χ x‖ * c := hmain
      _ = (∫ x : EuclideanSpace ℝ (Fin 3), ‖χ x‖) * c :=
            MeasureTheory.integral_mul_const c _
      _ = Cn * (1 + R) ^ n * (∫ x : EuclideanSpace ℝ (Fin 3), ‖χ x‖)
            * (1 + ‖u‖) ^ (-(n : ℤ)) := by
            rw [hc]; ring

end Work.PCFU
