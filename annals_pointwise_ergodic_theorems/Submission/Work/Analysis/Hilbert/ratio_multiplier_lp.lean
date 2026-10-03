import Mathlib
import Submission.Commons.Analysis.Convolution.eLpNorm_convolution_le
import Submission.Commons.Analysis.DiscreteCZ.discrete_convolution_lp_bounded_large
import Submission.Commons.Analysis.HardyLittlewood.discrete_maximal_lp
import Submission.Commons.Analysis.Hilbert.eLpNorm_le_liminf_of_le_liminf
import Submission.Commons.Analysis.Hilbert.radial_kernel_tsum_le_maximal
import Submission.Commons.Analysis.MeasureTheory.eLpNorm_iSup_of_monotone
import Submission.Commons.Analysis.Walsh.exists_khintchine_hilbert
import Submission.Port.Aesm

namespace Work.Analysis.Hilbert

open MeasureTheory
open scoped ENNReal BigOperators

/-! ## Auxiliary lemmas for `ratio_multiplier_lp` -/

/-- **Young's inequality for convolution on `ℤ`** with the counting measure: convolution by an
`ℓ¹` kernel is bounded on `ℓᵖ`, with the `ℓ¹` mass as constant. -/
lemma eLpNorm_conv_count_le {p : ℝ} (hp : 1 ≤ p) (K g : ℤ → ℂ) :
    eLpNorm (fun n : ℤ => ∑' z : ℤ, K z * g (n - z))
        (ENNReal.ofReal p) (Measure.count : Measure ℤ)
      ≤ (∑' t : ℤ, ENNReal.ofReal ‖K t‖) *
        eLpNorm g (ENNReal.ofReal p) (Measure.count : Measure ℤ) := by
  set μ : Measure ℤ := Measure.count with hμ
  have hpt : ∀ n : ℤ, ‖∑' z : ℤ, K z * g (n - z)‖ₑ
      ≤ ∑' z : ℤ, ‖K z‖ₑ * ‖g (n - z)‖ₑ := by
    intro n
    refine (enorm_tsum_le_tsum_enorm).trans (le_of_eq ?_)
    exact tsum_congr fun z => enorm_mul _ _
  have hstep1 : eLpNorm (fun n : ℤ => ∑' z : ℤ, K z * g (n - z)) (ENNReal.ofReal p) μ
      ≤ eLpNorm (fun n : ℤ => ∑' z : ℤ, ‖K z‖ₑ * ‖g (n - z)‖ₑ) (ENNReal.ofReal p) μ := by
    rw [show eLpNorm (fun n : ℤ => ∑' z : ℤ, K z * g (n - z)) (ENNReal.ofReal p) μ
        = eLpNorm (fun n : ℤ => ‖∑' z : ℤ, K z * g (n - z)‖ₑ) (ENNReal.ofReal p) μ
        from (eLpNorm_enorm (hf := by pw_aesm) _).symm]
    refine eLpNorm_mono_enorm_ae (hf := by pw_aesm) (Filter.Eventually.of_forall fun n => ?_)
    simpa only [enorm_eq_self] using hpt n
  have hstep2 : eLpNorm (fun n : ℤ => ∑' z : ℤ, ‖K z‖ₑ * ‖g (n - z)‖ₑ) (ENNReal.ofReal p) μ
      = eLpNorm (fun n : ℤ => ∫⁻ z : ℤ, ‖K z‖ₑ * ‖g (n - z)‖ₑ ∂μ) (ENNReal.ofReal p) μ := by
    congr 1
    funext n
    rw [hμ]
    exact (lintegral_count (fun z : ℤ => ‖K z‖ₑ * ‖g (n - z)‖ₑ)).symm
  have hreindex : (fun n : ℤ => ∫⁻ z : ℤ, ‖K z‖ₑ * ‖g (n - z)‖ₑ ∂μ)
      = fun n : ℤ => ∫⁻ y : ℤ, ‖K (n - y)‖ₑ * ‖g y‖ₑ ∂μ := by
    funext n
    rw [← lintegral_sub_left_eq_self (μ := μ)
      (f := fun z : ℤ => ‖K z‖ₑ * ‖g (n - z)‖ₑ) n]
    refine lintegral_congr fun y => ?_
    rw [show n - (n - y) = y from by ring]
  have hyoung := Commons.Analysis.Convolution.eLpNorm_convolution_le_ennreal (G := ℤ) (μ := μ)
    (K := fun z : ℤ => ‖K z‖ₑ) (Φ := fun y : ℤ => ‖g y‖ₑ)
    (p := p) (q := p) (r := 1) hp le_rfl (by ring : 1 / p = 1 / p + 1 / 1 - 1)
    (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable
  calc eLpNorm (fun n : ℤ => ∑' z : ℤ, K z * g (n - z)) (ENNReal.ofReal p) μ
      ≤ eLpNorm (fun n : ℤ => ∑' z : ℤ, ‖K z‖ₑ * ‖g (n - z)‖ₑ) (ENNReal.ofReal p) μ := hstep1
    _ = eLpNorm (fun n : ℤ => ∫⁻ z : ℤ, ‖K z‖ₑ * ‖g (n - z)‖ₑ ∂μ) (ENNReal.ofReal p) μ := hstep2
    _ = eLpNorm (fun n : ℤ => ∫⁻ y : ℤ, ‖K (n - y)‖ₑ * ‖g y‖ₑ ∂μ) (ENNReal.ofReal p) μ := by
        rw [hreindex]
    _ ≤ eLpNorm (fun z : ℤ => ‖K z‖ₑ) (ENNReal.ofReal 1) μ
          * eLpNorm (fun y : ℤ => ‖g y‖ₑ) (ENNReal.ofReal p) μ := hyoung
    _ = (∑' t : ℤ, ENNReal.ofReal ‖K t‖) * eLpNorm g (ENNReal.ofReal p) μ := by
        rw [show ENNReal.ofReal (1 : ℝ) = 1 by norm_num]
        rw [eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm), eLpNorm_enorm (hf := by pw_aesm), hμ, lintegral_count]
        rw [tsum_congr (fun t : ℤ => by rw [enorm_eq_self, ← ofReal_norm])]

end Work.Analysis.Hilbert
