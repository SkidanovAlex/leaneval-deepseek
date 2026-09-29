import Mathlib

namespace Work.TMComp.RealCartan

open MeasureTheory Set
open scoped ENNReal

set_option linter.unusedVariables false

/-- If the logarithmic potential `log (R / ‖z - t‖)` is integrable on a set `B ⊆ ℝ`, then `B` has
finite Lebesgue measure.

Indeed, away from the disc of radius `2R` around `z` the (negative) potential is bounded above by
`-log 2` in absolute value, so the part of `B` outside that bounded disc has finite measure by
Markov's inequality, while the part inside the disc is contained in a bounded interval. -/
theorem rcPot_volume_lt_top {B : Set ℝ} (hB : IsClosed B) {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hint : MeasureTheory.Integrable (fun t : ℝ => Real.log (R / ‖z - (t:ℂ)‖)) (MeasureTheory.volume.restrict B)) :
    MeasureTheory.volume B ≠ ⊤ := by
  let f : ℝ → ℝ := fun t => Real.log (R / ‖z - (t:ℂ)‖)
  have hcont : Continuous (fun t : ℝ => ‖z - (t:ℂ)‖) :=
    (continuous_const.sub Complex.continuous_ofReal).norm
  have hTmeas : MeasurableSet {t : ℝ | 2 * R < ‖z - (t:ℂ)‖} :=
    (isOpen_lt continuous_const hcont).measurableSet
  have hSmeas : MeasurableSet {t : ℝ | ‖z - (t:ℂ)‖ ≤ 2 * R} :=
    (isClosed_le hcont continuous_const).measurableSet
  have hST : {t : ℝ | ‖z - (t:ℂ)‖ ≤ 2 * R}ᶜ = {t : ℝ | 2 * R < ‖z - (t:ℂ)‖} := by
    ext t
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc0 : ENNReal.ofReal (Real.log 2) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]; exact hlog2pos
  have hct : ENNReal.ofReal (Real.log 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  -- Markov's inequality: the set where `‖f‖ₑ ≥ log 2` has finite measure
  have hfin : ∫⁻ t, ‖f t‖ₑ ∂(volume.restrict B) < ⊤ := hint.hasFiniteIntegral
  have hg : AEMeasurable (fun t : ℝ => ‖f t‖ₑ) (volume.restrict B) :=
    hint.aestronglyMeasurable.enorm
  have hU : (volume.restrict B) {t : ℝ | ENNReal.ofReal (Real.log 2) ≤ ‖f t‖ₑ} < ⊤ := by
    refine lt_of_le_of_lt (meas_ge_le_lintegral_div (μ := volume.restrict B)
      (f := fun t : ℝ => ‖f t‖ₑ) (ε := ENNReal.ofReal (Real.log 2)) hg hc0 hct) ?_
    exact ENNReal.div_lt_top (ne_of_lt hfin) hc0
  -- off the disc of radius `2R`, the potential is `≤ -log 2`
  have hTsub : {t : ℝ | 2 * R < ‖z - (t:ℂ)‖}
      ⊆ {t : ℝ | ENNReal.ofReal (Real.log 2) ≤ ‖f t‖ₑ} := by
    intro t ht
    change ENNReal.ofReal (Real.log 2) ≤ ‖f t‖ₑ
    have ht' : 2 * R < ‖z - (t:ℂ)‖ := ht
    have hpos : 0 < ‖z - (t:ℂ)‖ := by linarith
    have hhalf : R / ‖z - (t:ℂ)‖ < 1 / 2 := by
      rw [div_lt_iff₀ hpos]; linarith
    have h1 : f t ≤ Real.log (1 / 2) :=
      Real.log_le_log (div_pos hR hpos) (le_of_lt hhalf)
    have h2 : Real.log (1 / 2 : ℝ) = - Real.log 2 := by rw [one_div, Real.log_inv]
    have hfle : f t ≤ - Real.log 2 := by linarith
    have hfneg : f t < 0 := by linarith
    have habs : Real.log 2 ≤ |f t| := by rw [abs_of_neg hfneg]; linarith
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal habs
  have hμT : (volume.restrict B) {t : ℝ | 2 * R < ‖z - (t:ℂ)‖} < ⊤ :=
    lt_of_le_of_lt (measure_mono hTsub) hU
  have hTfin : volume ({t : ℝ | 2 * R < ‖z - (t:ℂ)‖} ∩ B) < ⊤ := by
    rwa [Measure.restrict_apply hTmeas] at hμT
  have hBcapT : volume (B ∩ {t : ℝ | 2 * R < ‖z - (t:ℂ)‖}) < ⊤ := by
    rw [Set.inter_comm] at hTfin
    exact hTfin
  -- the disc of radius `2R` is bounded
  have hSsub : {t : ℝ | ‖z - (t:ℂ)‖ ≤ 2 * R}
      ⊆ Set.Icc (z.re - 2 * R) (z.re + 2 * R) := by
    intro t ht
    have ht' : ‖z - (t:ℂ)‖ ≤ 2 * R := ht
    have h1 : |z.re - t| ≤ ‖z - (t:ℂ)‖ := by
      have h := Complex.abs_re_le_norm (z - (t : ℂ))
      simpa using h
    have h2 : |z.re - t| ≤ 2 * R := le_trans h1 ht'
    rw [Set.mem_Icc]
    have h2' := abs_le.mp h2
    constructor <;> linarith [h2'.1, h2'.2]
  have hSfin : volume {t : ℝ | ‖z - (t:ℂ)‖ ≤ 2 * R} < ⊤ := by
    calc volume {t : ℝ | ‖z - (t:ℂ)‖ ≤ 2 * R}
        ≤ volume (Set.Icc (z.re - 2 * R) (z.re + 2 * R)) := measure_mono hSsub
      _ = ENNReal.ofReal ((z.re + 2 * R) - (z.re - 2 * R)) := Real.volume_Icc
      _ < ⊤ := ENNReal.ofReal_lt_top
  have hBcapS : volume (B ∩ {t : ℝ | ‖z - (t:ℂ)‖ ≤ 2 * R}) < ⊤ :=
    lt_of_le_of_lt (measure_mono Set.inter_subset_right) hSfin
  -- assemble the two pieces
  have hdiff : B \ {t : ℝ | ‖z - (t:ℂ)‖ ≤ 2 * R} = B ∩ {t : ℝ | 2 * R < ‖z - (t:ℂ)‖} := by
    ext t
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq, not_le]
  have hsplit : volume B = volume (B ∩ {t : ℝ | ‖z - (t:ℂ)‖ ≤ 2 * R})
      + volume (B ∩ {t : ℝ | 2 * R < ‖z - (t:ℂ)‖}) := by
    have h1 := measure_inter_add_sdiff (μ := volume) B hSmeas
    rw [hdiff] at h1
    exact h1.symm
  exact ne_of_lt (by rw [hsplit]; exact ENNReal.add_lt_top.mpr ⟨hBcapS, hBcapT⟩)

end Work.TMComp.RealCartan
