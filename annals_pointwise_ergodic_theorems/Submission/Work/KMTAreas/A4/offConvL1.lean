import Mathlib
import Submission.Commons.Analysis.Convolution.eLpNorm_convolution_le
import Submission.Port.Aesm

namespace Work.KMTAreas.A4

open MeasureTheory
open Filter
open scoped ENNReal

theorem offConvL1 (u v : SchwartzMap ℝ ℂ) :
    ∫ x : ℝ, ‖SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) u v x‖
      ≤ (∫ x : ℝ, ‖u x‖) * (∫ x : ℝ, ‖v x‖) := by
  have hEq : (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) u v : ℝ → ℂ)
      = fun x : ℝ => ∫ t : ℝ, u t * v (x - t) := by
    funext x
    rw [SchwartzMap.convolution_apply, MeasureTheory.convolution_def]
    simp only [ContinuousLinearMap.mul_apply']
  rw [hEq]
  set A : ℝ := ∫ x : ℝ, ‖u x‖ with hA
  set B : ℝ := ∫ x : ℝ, ‖v x‖ with hB
  have hInt : Integrable (fun x : ℝ => ∫ t : ℝ, u t * v (x - t)) volume := by
    rw [← hEq]
    exact (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) u v).integrable
  have hA0 : 0 ≤ A := by
    rw [hA]; exact integral_nonneg fun x => norm_nonneg _
  have hB0 : 0 ≤ B := by
    rw [hB]; exact integral_nonneg fun x => norm_nonneg _
  have hmain : ENNReal.ofReal (∫ x : ℝ, ‖∫ t : ℝ, u t * v (x - t)‖)
      ≤ ENNReal.ofReal (A * B) := by
    rw [ofReal_integral_norm_eq_lintegral_enorm hInt]
    have hpt : ∀ x : ℝ, ‖∫ t : ℝ, u t * v (x - t)‖ₑ
        ≤ ∫⁻ y : ℝ, ‖u (x - y)‖ₑ * ‖v y‖ₑ := by
      intro x
      calc ‖∫ t : ℝ, u t * v (x - t)‖ₑ
          ≤ ∫⁻ t : ℝ, ‖u t * v (x - t)‖ₑ := enorm_integral_le_lintegral_enorm _
        _ = ∫⁻ t : ℝ, ‖u t‖ₑ * ‖v (x - t)‖ₑ := lintegral_congr fun t => enorm_mul _ _
        _ = ∫⁻ y : ℝ, ‖u (x - y)‖ₑ * ‖v y‖ₑ := by
              rw [← lintegral_sub_left_eq_self (fun y : ℝ => ‖u (x - y)‖ₑ * ‖v y‖ₑ) x]
              exact lintegral_congr fun t => by rw [show x - (x - t) = t from by ring]
    have hmono : eLpNorm (fun x : ℝ => ∫ t : ℝ, u t * v (x - t)) 1 volume
        ≤ eLpNorm (fun x : ℝ => ∫⁻ y : ℝ, ‖u (x - y)‖ₑ * ‖v y‖ₑ) 1 volume := by
      rw [← eLpNorm_enorm (hf := hInt.aestronglyMeasurable) (f := fun x : ℝ => ∫ t : ℝ, u t * v (x - t)) (p := 1) (μ := volume)]
      refine eLpNorm_mono_enorm_ae (hf := hInt.aestronglyMeasurable.enorm.aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
      simpa only [enorm_eq_self] using hpt x
    have hyoung := Commons.Analysis.Convolution.eLpNorm_convolution_le_ennreal (G := ℝ) (μ := volume)
      (K := fun x : ℝ => ‖u x‖ₑ) (Φ := fun x : ℝ => ‖v x‖ₑ) (p := 1) (q := 1) (r := 1)
      le_rfl le_rfl (by norm_num) (u.continuous.aemeasurable.enorm) (v.continuous.aemeasurable.enorm)
    simp only [ENNReal.ofReal_one] at hyoung
    have hKu : eLpNorm (fun x : ℝ => ‖u x‖ₑ) 1 volume = ENNReal.ofReal A := by
      rw [eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm)]
      simp only [enorm_eq_self]
      rw [hA]
      exact (ofReal_integral_norm_eq_lintegral_enorm (f := (u : ℝ → ℂ)) u.integrable).symm
    have hKv : eLpNorm (fun x : ℝ => ‖v x‖ₑ) 1 volume = ENNReal.ofReal B := by
      rw [eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm)]
      simp only [enorm_eq_self]
      rw [hB]
      exact (ofReal_integral_norm_eq_lintegral_enorm (f := (v : ℝ → ℂ)) v.integrable).symm
    calc ∫⁻ x : ℝ, ‖∫ t : ℝ, u t * v (x - t)‖ₑ
        = eLpNorm (fun x : ℝ => ∫ t : ℝ, u t * v (x - t)) 1 volume :=
          (eLpNorm_one_eq_lintegral_enorm (hf := hInt.aestronglyMeasurable)).symm
      _ ≤ eLpNorm (fun x : ℝ => ∫⁻ y : ℝ, ‖u (x - y)‖ₑ * ‖v y‖ₑ) 1 volume := hmono
      _ ≤ eLpNorm (fun x : ℝ => ‖u x‖ₑ) 1 volume * eLpNorm (fun x : ℝ => ‖v x‖ₑ) 1 volume :=
          hyoung
      _ = ENNReal.ofReal A * ENNReal.ofReal B := by rw [hKu, hKv]
      _ = ENNReal.ofReal (A * B) := (ENNReal.ofReal_mul hA0).symm
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hA0 hB0)).mp hmain

end Work.KMTAreas.A4
