import Mathlib
import Submission.Commons.Analysis.Convolution.eLpNorm_convolution_le
import Submission.Commons.Analysis.Fourier.mikhlin_multiplier_lp

namespace Work.BourgainPlan.Maximal

open MeasureTheory
open scoped ENNReal

/-- Given `k ∈ L¹(ℝ)` and `u ∈ Lᵖ(ℝ)` with `1 ≤ p`, the convolution integrand
`y ↦ k (x - y) * u y` is integrable for almost every `x`.

This is the a.e. existence of the convolution `k * u` at the level of the integrand
(as opposed to a.e. finiteness of the convolution itself). -/
theorem aeIntegrableMulSubOfMemLp {p : ℝ} (hp : 1 ≤ p) {k u : ℝ → ℂ}
    (hk : MeasureTheory.MemLp k 1 (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (hu : MeasureTheory.MemLp u (ENNReal.ofReal p) (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      MeasureTheory.Integrable (fun y : ℝ => k (x - y) * u y)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  have hp_ne : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
  have hp_top : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  let K : ℝ → ℝ≥0∞ := fun t => ‖k t‖ₑ
  let U : ℝ → ℝ≥0∞ := fun t => ‖u t‖ₑ
  have hKae : AEMeasurable K volume := hk.aestronglyMeasurable.enorm
  have hUae : AEMeasurable U volume := hu.aestronglyMeasurable.enorm
  -- Young's inequality for convolutions, in the `L¹ * Lᵖ ⊆ Lᵖ` case.
  have hYoung := Commons.Analysis.Convolution.eLpNorm_convolution_le_ennreal (G := ℝ) (μ := volume)
    (K := K) (Φ := U) (p := p) (q := p) (r := 1) hp le_rfl (by ring) hKae hUae
  have hKlt : eLpNorm K (ENNReal.ofReal (1 : ℝ)) volume < ⊤ := by
    rw [show ENNReal.ofReal (1 : ℝ) = 1 by norm_num]
    have h : eLpNorm K 1 volume = eLpNorm k 1 volume := by
      show eLpNorm (fun t => ‖k t‖ₑ) 1 volume = eLpNorm k 1 volume
      rw [eLpNorm_enorm _ hk.aestronglyMeasurable]
    rw [h]
    exact hk.eLpNorm_lt_top
  have hUlt : eLpNorm U (ENNReal.ofReal p) volume < ⊤ := by
    have h : eLpNorm U (ENNReal.ofReal p) volume = eLpNorm u (ENNReal.ofReal p) volume := by
      show eLpNorm (fun t => ‖u t‖ₑ) (ENNReal.ofReal p) volume = eLpNorm u (ENNReal.ofReal p) volume
      rw [eLpNorm_enorm _ hu.aestronglyMeasurable]
    rw [h]
    exact hu.eLpNorm_lt_top
  have hWlt : eLpNorm (fun x => ∫⁻ y, K (x - y) * U y ∂volume) (ENNReal.ofReal p) volume < ⊤ :=
    lt_of_le_of_lt hYoung (ENNReal.mul_lt_top hKlt hUlt)
  have hWae : AEMeasurable (fun x => ∫⁻ y, K (x - y) * U y ∂volume) volume := by
    have hAM : AEMeasurable (fun z : ℝ × ℝ => K (z.1 - z.2) * U z.2) (volume.prod volume) :=
      ((hKae.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_of_right_invariant volume volume)).mul hUae.comp_snd)
    exact hAM.lintegral_prod_right'
  -- Hence the convolution is finite a.e., and `W x < ⊤` is exactly the finiteness
  -- of the integral of the norm of the integrand at `x`.
  have hWfin : ∀ᵐ x ∂volume, (∫⁻ y, K (x - y) * U y ∂volume) < ⊤ := by
    have hint : (∫⁻ x, (∫⁻ y, K (x - y) * U y ∂volume) ^ p ∂volume) ≠ ⊤ := by
      intro hcon
      have heq : eLpNorm (fun x => ∫⁻ y, K (x - y) * U y ∂volume) (ENNReal.ofReal p) volume
          = (∫⁻ x, (∫⁻ y, K (x - y) * U y ∂volume) ^ p ∂volume) ^ (1 / p) := by
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne hp_top hWae.aestronglyMeasurable]
        simp only [ENNReal.toReal_ofReal hp0.le, enorm_eq_self]
      rw [heq, hcon, ENNReal.top_rpow_of_pos (one_div_pos.mpr hp0)] at hWlt
      exact lt_irrefl ⊤ hWlt
    have h := ae_lt_top' (hWae.pow_const p) hint
    filter_upwards [h] with x hx
    rwa [ENNReal.rpow_lt_top_iff_of_pos hp0] at hx
  filter_upwards [hWfin] with x hx
  refine ⟨?_, ?_⟩
  · exact (hk.aestronglyMeasurable.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_left_of_right_invariant volume x)).mul hu.aestronglyMeasurable
  · show (∫⁻ y, ‖k (x - y) * u y‖ₑ ∂volume) < ⊤
    have heq : (fun y => ‖k (x - y) * u y‖ₑ) = fun y => K (x - y) * U y := by
      funext y
      rw [enorm_mul]
    rw [heq]
    exact hx

end Work.BourgainPlan.Maximal
