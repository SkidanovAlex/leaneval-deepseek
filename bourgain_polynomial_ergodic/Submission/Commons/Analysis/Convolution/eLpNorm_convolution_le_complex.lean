import Mathlib
import Submission.Commons.Analysis.Convolution.eLpNorm_convolution_le

namespace Commons.Analysis.Convolution

open MeasureTheory
open _root_.MeasureTheory
open scoped FourierTransform ENNReal BigOperators

/-- **Young's inequality for convolutions with `ℂ`-valued kernels on `ℝ`.**  For `k ∈ L¹(ℝ,ℂ)`
and `f ∈ L^p(ℝ,ℂ)` (`p ≥ 1`), the convolution `x ↦ ∫ y, k (x - y) * f y` satisfies
`‖k * f‖_{L^p} ≤ ‖k‖_{L¹} ‖f‖_{L^p}`.

(The commons has `Commons.Analysis.Convolution.eLpNorm_convolution_le` for `ℝ`-valued `k`
factored through `eLpNorm_convolution_le_ennreal`; this is the `ℂ`-valued form, obtained from
the same `ℝ≥0∞`-valued statement with `K = ‖k‖ₑ`, `Φ = ‖f‖ₑ` and the pointwise bound
`‖∫ y, k (x-y) * f y‖ₑ ≤ ∫⁻ y, ‖k (x-y)‖ₑ * ‖f y‖ₑ`.) -/
theorem eLpNorm_convolution_le_complex (k f : ℝ → ℂ) (p : ℝ) (hp : 1 ≤ p)
    (hk : MeasureTheory.MemLp k 1 (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal p)
      (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    MeasureTheory.eLpNorm (fun x : ℝ => ∫ y, k (x - y) * f y) (ENNReal.ofReal p)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)
      ≤ MeasureTheory.eLpNorm k 1 (MeasureTheory.volume : MeasureTheory.Measure ℝ)
        * MeasureTheory.eLpNorm f (ENNReal.ofReal p) (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  set K : ℝ → ℝ≥0∞ := fun z => ‖k z‖ₑ with hKdef
  set Φ : ℝ → ℝ≥0∞ := fun y => ‖f y‖ₑ with hΦdef
  have hKae : AEMeasurable K (volume : Measure ℝ) := by
    rw [hKdef]; exact hk.aestronglyMeasurable.enorm
  have hFae : AEMeasurable Φ (volume : Measure ℝ) := by
    rw [hΦdef]; exact hf.aestronglyMeasurable.enorm
  have h1 : ∀ x : ℝ, ‖(∫ y, k (x - y) * f y)‖ₑ ≤ ∫⁻ y, K (x - y) * Φ y := by
    intro x
    refine (enorm_integral_le_lintegral_enorm (fun y => k (x - y) * f y)).trans (le_of_eq ?_)
    apply lintegral_congr; intro y
    rw [enorm_mul, hKdef, hΦdef]
  have hpqr : 1 / p = 1 / p + 1 / 1 - 1 := by ring
  have hconv_meas : AEStronglyMeasurable (fun x : ℝ => ∫ y, k (x - y) * f y) volume := by
    have hF : AEStronglyMeasurable (fun z : ℝ × ℝ => k (z.1 - z.2) * f z.2)
        ((volume : Measure ℝ).prod volume) :=
      (hk.aestronglyMeasurable.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_of_right_invariant volume volume)).mul
        hf.aestronglyMeasurable.comp_snd
    exact hF.integral_prod_right'
  calc MeasureTheory.eLpNorm (fun x : ℝ => ∫ y, k (x - y) * f y) (ENNReal.ofReal p)
          (volume : Measure ℝ)
      ≤ MeasureTheory.eLpNorm (fun x : ℝ => ∫⁻ y, K (x - y) * Φ y) (ENNReal.ofReal p)
          (volume : Measure ℝ) :=
        eLpNorm_mono_enorm_ae hconv_meas (Filter.Eventually.of_forall h1)
    _ ≤ MeasureTheory.eLpNorm K (ENNReal.ofReal 1) (volume : Measure ℝ)
          * MeasureTheory.eLpNorm Φ (ENNReal.ofReal p) (volume : Measure ℝ) :=
        eLpNorm_convolution_le_ennreal (p := p) (q := p) (r := 1) hp le_rfl hpqr hKae hFae
    _ = MeasureTheory.eLpNorm k 1 (volume : Measure ℝ)
          * MeasureTheory.eLpNorm f (ENNReal.ofReal p) (volume : Measure ℝ) := by
        simp only [hKdef, hΦdef, MeasureTheory.eLpNorm_enorm _ hk.aestronglyMeasurable,
          MeasureTheory.eLpNorm_enorm _ hf.aestronglyMeasurable, ENNReal.ofReal_one]

end Commons.Analysis.Convolution
