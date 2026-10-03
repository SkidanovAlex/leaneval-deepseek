import Mathlib
import Submission.Commons.Analysis.Convolution.eLpNorm_convolution_le
import Submission.Port.Aesm

namespace Work.KMTAreas.A4

set_option maxHeartbeats 1000000

open MeasureTheory
open scoped ENNReal

/-- **Young's convolution inequality on `ℤ` for the counting measure.**  Convolution by an `ℓ¹`
kernel is bounded on `ℓᵖ` with the `ℓ¹` mass of the kernel as constant.  The constant is written
in `ℝ≥0∞` form so that no summability hypothesis on the kernel is needed. -/
theorem offYoung_conv_count_le {p : ℝ} (hp : 1 ≤ p) (K g : ℤ → ℂ) :
    eLpNorm (fun n : ℤ => ∑' z : ℤ, K z * g (n - z)) (ENNReal.ofReal p)
        (Measure.count : Measure ℤ)
      ≤ (∑' t : ℤ, ENNReal.ofReal ‖K t‖) *
        eLpNorm g (ENNReal.ofReal p) (Measure.count : Measure ℤ) := by
  have hpt : ∀ n : ℤ, ‖∑' z : ℤ, K z * g (n - z)‖ₑ
      ≤ ∑' z : ℤ, ‖K z‖ₑ * ‖g (n - z)‖ₑ := by
    intro n
    refine (enorm_tsum_le_tsum_enorm).trans (le_of_eq ?_)
    exact tsum_congr fun z => enorm_mul _ _
  have hstep1 : eLpNorm (fun n : ℤ => ∑' z : ℤ, K z * g (n - z)) (ENNReal.ofReal p)
        (Measure.count : Measure ℤ)
      ≤ eLpNorm (fun n : ℤ => ∑' z : ℤ, ‖K z‖ₑ * ‖g (n - z)‖ₑ) (ENNReal.ofReal p)
        (Measure.count : Measure ℤ) := by
    rw [show eLpNorm (fun n : ℤ => ∑' z : ℤ, K z * g (n - z)) (ENNReal.ofReal p)
        (Measure.count : Measure ℤ)
        = eLpNorm (fun n : ℤ => ‖∑' z : ℤ, K z * g (n - z)‖ₑ) (ENNReal.ofReal p)
        (Measure.count : Measure ℤ) from (eLpNorm_enorm (hf := by pw_aesm) _).symm]
    refine eLpNorm_mono_enorm_ae (hf := by pw_aesm) (Filter.Eventually.of_forall fun n => ?_)
    simpa only [enorm_eq_self] using hpt n
  have hstep2 : eLpNorm (fun n : ℤ => ∑' z : ℤ, ‖K z‖ₑ * ‖g (n - z)‖ₑ) (ENNReal.ofReal p)
        (Measure.count : Measure ℤ)
      = eLpNorm (fun n : ℤ => ∫⁻ z : ℤ, ‖K z‖ₑ * ‖g (n - z)‖ₑ
          ∂(Measure.count : Measure ℤ)) (ENNReal.ofReal p) (Measure.count : Measure ℤ) := by
    congr 1
    funext n
    exact (lintegral_count (fun z : ℤ => ‖K z‖ₑ * ‖g (n - z)‖ₑ)).symm
  have hreindex : (fun n : ℤ => ∫⁻ z : ℤ, ‖K z‖ₑ * ‖g (n - z)‖ₑ
        ∂(Measure.count : Measure ℤ))
      = fun n : ℤ => ∫⁻ y : ℤ, ‖K (n - y)‖ₑ * ‖g y‖ₑ ∂(Measure.count : Measure ℤ) := by
    funext n
    rw [← lintegral_sub_left_eq_self (μ := (Measure.count : Measure ℤ))
      (f := fun z : ℤ => ‖K z‖ₑ * ‖g (n - z)‖ₑ) n]
    refine lintegral_congr fun y => ?_
    rw [show n - (n - y) = y from by ring]
  have hyoung := Commons.Analysis.Convolution.eLpNorm_convolution_le_ennreal (G := ℤ)
    (μ := (Measure.count : Measure ℤ))
    (K := fun z : ℤ => ‖K z‖ₑ) (Φ := fun y : ℤ => ‖g y‖ₑ)
    (p := p) (q := p) (r := 1) hp le_rfl (by ring : 1 / p = 1 / p + 1 / 1 - 1)
    (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable
  calc eLpNorm (fun n : ℤ => ∑' z : ℤ, K z * g (n - z)) (ENNReal.ofReal p)
        (Measure.count : Measure ℤ)
      ≤ eLpNorm (fun n : ℤ => ∑' z : ℤ, ‖K z‖ₑ * ‖g (n - z)‖ₑ) (ENNReal.ofReal p)
          (Measure.count : Measure ℤ) := hstep1
    _ = eLpNorm (fun n : ℤ => ∫⁻ z : ℤ, ‖K z‖ₑ * ‖g (n - z)‖ₑ
          ∂(Measure.count : Measure ℤ)) (ENNReal.ofReal p) (Measure.count : Measure ℤ) := hstep2
    _ = eLpNorm (fun n : ℤ => ∫⁻ y : ℤ, ‖K (n - y)‖ₑ * ‖g y‖ₑ
          ∂(Measure.count : Measure ℤ)) (ENNReal.ofReal p) (Measure.count : Measure ℤ) := by
        rw [hreindex]
    _ ≤ eLpNorm (fun z : ℤ => ‖K z‖ₑ) (ENNReal.ofReal 1) (Measure.count : Measure ℤ)
          * eLpNorm (fun y : ℤ => ‖g y‖ₑ) (ENNReal.ofReal p)
              (Measure.count : Measure ℤ) := hyoung
    _ = (∑' t : ℤ, ENNReal.ofReal ‖K t‖) * eLpNorm g (ENNReal.ofReal p)
          (Measure.count : Measure ℤ) := by
        rw [show ENNReal.ofReal (1 : ℝ) = 1 by norm_num]
        rw [eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm), eLpNorm_enorm (hf := by pw_aesm), lintegral_count]
        rw [tsum_congr (fun t : ℤ => by rw [enorm_eq_self, ← ofReal_norm])]

theorem offYoung {κ : ℤ → ℂ} (hκ : Summable fun j : ℤ => ‖κ j‖) {q : ℝ} (hq : 1 ≤ q) :
    ∀ f : ℤ → ℂ, (Function.support f).Finite →
      MeasureTheory.eLpNorm (fun n : ℤ => ∑' j : ℤ, κ j * f (n - j)) (ENNReal.ofReal q)
          MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (∑' j : ℤ, ‖κ j‖) *
            MeasureTheory.eLpNorm f (ENNReal.ofReal q) MeasureTheory.Measure.count := by
  intro f _
  have h := offYoung_conv_count_le hq κ f
  have hof : (∑' t : ℤ, ENNReal.ofReal ‖κ t‖) = ENNReal.ofReal (∑' j : ℤ, ‖κ j‖) :=
    (ENNReal.ofReal_tsum_of_nonneg (f := fun j : ℤ => ‖κ j‖) (fun t : ℤ => norm_nonneg (κ t)) hκ).symm
  rw [hof] at h
  exact h

end Work.KMTAreas.A4
