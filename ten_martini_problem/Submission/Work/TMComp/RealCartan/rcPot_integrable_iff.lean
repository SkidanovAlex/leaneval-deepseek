import Mathlib

namespace Work.TMComp.RealCartan

open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- If `B ⊆ ℝ` is closed and `z : ℂ` does not lie in the image of `B` under the inclusion
`ℝ → ℂ`, then `‖z - t‖` is uniformly bounded below on `B`. -/
theorem rcPot_dist_pos {B : Set ℝ} (hB : IsClosed B) {z : ℂ} (hz : z ∉ Complex.ofReal '' B) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ B, δ ≤ ‖z - (t : ℂ)‖ := by
  by_cases him : z.im = 0
  · have hzre : z = ((z.re : ℝ) : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using him
    have hzreB : z.re ∉ B := by
      intro hb
      exact hz (by rw [hzre]; exact ⟨z.re, hb, rfl⟩)
    obtain ⟨ε, hε, hball⟩ := (Metric.isOpen_iff.mp hB.isOpen_compl) z.re hzreB
    refine ⟨ε, hε, ?_⟩
    intro t ht
    have htnot : t ∉ Metric.ball z.re ε := fun hmem => hball hmem ht
    rw [Metric.mem_ball, not_lt] at htnot
    have hdist : ε ≤ dist z.re t := by rw [dist_comm]; exact htnot
    rw [Real.dist_eq] at hdist
    have hnorm : ‖z - (t : ℂ)‖ = |z.re - t| := by
      rw [hzre, show ((z.re : ℂ) - (t : ℂ)) = ((z.re - t : ℝ) : ℂ) by
            rw [Complex.ofReal_sub]]
      exact RCLike.norm_ofReal (z.re - t)
    rw [hnorm]
    exact hdist
  · refine ⟨|z.im|, abs_pos.mpr him, ?_⟩
    intro t _
    have h := Complex.abs_im_le_norm (z - (t : ℂ))
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at h
    exact h

/-- The logarithmic potentials `log (R / ‖z - t‖)` and `log (R / ‖w - t‖)` differ by a bounded
amount on any `B` on which `‖z - t‖` and `‖w - t‖` are bounded below by positive constants. -/
theorem rcPot_log_diff_bounded {B : Set ℝ} {R δz δw : ℝ} (hR : 0 < R) (hδz : 0 < δz)
    (hδw : 0 < δw) {z w : ℂ} (hz : ∀ t ∈ B, δz ≤ ‖z - (t : ℂ)‖)
    (hw : ∀ t ∈ B, δw ≤ ‖w - (t : ℂ)‖) :
    ∃ M : ℝ, ∀ t ∈ B,
      |Real.log (R / ‖z - (t : ℂ)‖) - Real.log (R / ‖w - (t : ℂ)‖)| ≤ M := by
  refine ⟨max (Real.log (1 + ‖w - z‖ / δz)) (Real.log (1 + ‖w - z‖ / δw)), ?_⟩
  intro t ht
  have hzt : 0 < ‖z - (t : ℂ)‖ := lt_of_lt_of_le hδz (hz t ht)
  have hwt : 0 < ‖w - (t : ℂ)‖ := lt_of_lt_of_le hδw (hw t ht)
  have hdiff : Real.log (R / ‖z - (t:ℂ)‖) - Real.log (R / ‖w - (t:ℂ)‖)
      = Real.log (‖w - (t:ℂ)‖ / ‖z - (t:ℂ)‖) := by
    rw [Real.log_div (ne_of_gt hR) (ne_of_gt hzt), Real.log_div (ne_of_gt hR) (ne_of_gt hwt),
        Real.log_div (ne_of_gt hwt) (ne_of_gt hzt)]
    ring
  have htri1 : ‖w - (t:ℂ)‖ ≤ ‖w - z‖ + ‖z - (t:ℂ)‖ := by
    calc ‖w - (t:ℂ)‖ = ‖(w - z) + (z - (t:ℂ))‖ := by congr 1; abel
      _ ≤ ‖w - z‖ + ‖z - (t:ℂ)‖ := norm_add_le _ _
  have hba1 : ‖w - (t:ℂ)‖ / ‖z - (t:ℂ)‖ ≤ 1 + ‖w - z‖ / δz := by
    have h2 : ‖w - z‖ ≤ ‖w - z‖ / δz * ‖z - (t:ℂ)‖ := by
      have hle : 1 ≤ ‖z - (t:ℂ)‖ / δz := (le_div_iff₀ hδz).mpr (by simpa using hz t ht)
      calc ‖w - z‖ = ‖w - z‖ * 1 := (mul_one _).symm
        _ ≤ ‖w - z‖ * (‖z - (t:ℂ)‖ / δz) := mul_le_mul_of_nonneg_left hle (norm_nonneg _)
        _ = ‖w - z‖ / δz * ‖z - (t:ℂ)‖ := by ring
    rw [div_le_iff₀ hzt, add_mul, one_mul]
    linarith [htri1, h2]
  have htri2 : ‖z - (t:ℂ)‖ ≤ ‖z - w‖ + ‖w - (t:ℂ)‖ := by
    calc ‖z - (t:ℂ)‖ = ‖(z - w) + (w - (t:ℂ))‖ := by congr 1; abel
      _ ≤ ‖z - w‖ + ‖w - (t:ℂ)‖ := norm_add_le _ _
  have hba2 : ‖z - (t:ℂ)‖ / ‖w - (t:ℂ)‖ ≤ 1 + ‖z - w‖ / δw := by
    have h2 : ‖z - w‖ ≤ ‖z - w‖ / δw * ‖w - (t:ℂ)‖ := by
      have hle : 1 ≤ ‖w - (t:ℂ)‖ / δw := (le_div_iff₀ hδw).mpr (by simpa using hw t ht)
      calc ‖z - w‖ = ‖z - w‖ * 1 := (mul_one _).symm
        _ ≤ ‖z - w‖ * (‖w - (t:ℂ)‖ / δw) := mul_le_mul_of_nonneg_left hle (norm_nonneg _)
        _ = ‖z - w‖ / δw * ‖w - (t:ℂ)‖ := by ring
    rw [div_le_iff₀ hwt, add_mul, one_mul]
    linarith [htri2, h2]
  have hL1 : Real.log (‖w - (t:ℂ)‖ / ‖z - (t:ℂ)‖) ≤ Real.log (1 + ‖w - z‖ / δz) :=
    Real.log_le_log (div_pos hwt hzt) hba1
  have hL2 : Real.log (‖z - (t:ℂ)‖ / ‖w - (t:ℂ)‖) ≤ Real.log (1 + ‖z - w‖ / δw) :=
    Real.log_le_log (div_pos hzt hwt) hba2
  have hL2' : Real.log (‖z - (t:ℂ)‖ / ‖w - (t:ℂ)‖) ≤ Real.log (1 + ‖w - z‖ / δw) := by
    simpa [norm_sub_rev] using hL2
  have hM1 : Real.log (‖w - (t:ℂ)‖ / ‖z - (t:ℂ)‖)
      ≤ max (Real.log (1 + ‖w - z‖ / δz)) (Real.log (1 + ‖w - z‖ / δw)) :=
    le_trans hL1 (le_max_left _ _)
  have hM2 : -Real.log (‖w - (t:ℂ)‖ / ‖z - (t:ℂ)‖)
      ≤ max (Real.log (1 + ‖w - z‖ / δz)) (Real.log (1 + ‖w - z‖ / δw)) := by
    have heq : -Real.log (‖w - (t:ℂ)‖ / ‖z - (t:ℂ)‖)
        = Real.log (‖z - (t:ℂ)‖ / ‖w - (t:ℂ)‖) := by
      rw [Real.log_div (ne_of_gt hwt) (ne_of_gt hzt), Real.log_div (ne_of_gt hzt) (ne_of_gt hwt)]
      ring
    rw [heq]
    exact le_trans hL2' (le_max_right _ _)
  have habs : |Real.log (‖w - (t:ℂ)‖ / ‖z - (t:ℂ)‖)|
      ≤ max (Real.log (1 + ‖w - z‖ / δz)) (Real.log (1 + ‖w - z‖ / δw)) :=
    abs_le.mpr ⟨by linarith [hM2], hM1⟩
  rw [hdiff]
  exact habs

/-- If `t ↦ log (R / ‖z - t‖)` is integrable over `volume.restrict B`, then `B` has finite
Lebesgue measure.  (Otherwise the integrand has modulus at least `log 2` on a part of `B`
carrying infinite measure.) -/
theorem rcPot_measure_lt_top_of_integrable {B : Set ℝ} {R : ℝ} (hR : 0 < R) {z : ℂ}
    (h : MeasureTheory.Integrable (fun t : ℝ => Real.log (R / ‖z - (t : ℂ)‖))
      (MeasureTheory.volume.restrict B)) :
    MeasureTheory.volume B < ⊤ := by
  set A : Set ℝ := {t | 2 * R ≤ ‖z - (t : ℂ)‖} with hAdef
  have hAmem : ∀ t : ℝ, t ∈ A ↔ 2 * R ≤ ‖z - (t : ℂ)‖ := fun t => by
    rw [hAdef, Set.mem_ofPred_eq]
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hAmeas : MeasurableSet A := by
    rw [hAdef]
    exact measurableSet_le measurable_const
      ((continuous_const.sub Complex.continuous_ofReal).norm.measurable)
  have hpt : ∀ t ∈ A, ENNReal.ofReal (Real.log 2)
      ≤ ‖Real.log (R / ‖z - (t : ℂ)‖)‖ₑ := by
    intro t ht
    have ht' : 2 * R ≤ ‖z - (t : ℂ)‖ := (hAmem t).mp ht
    have hzpos : 0 < ‖z - (t : ℂ)‖ := lt_of_lt_of_le (by linarith) ht'
    have hratio_pos : 0 < R / ‖z - (t : ℂ)‖ := div_pos hR hzpos
    have hratio_le : R / ‖z - (t : ℂ)‖ ≤ 1 / 2 := by
      rw [div_le_iff₀ hzpos]; linarith
    have hlogle : Real.log (R / ‖z - (t : ℂ)‖) ≤ Real.log (1 / 2) :=
      Real.log_le_log hratio_pos hratio_le
    have hlt : Real.log (R / ‖z - (t : ℂ)‖) < 0 :=
      lt_of_le_of_lt hlogle (by rw [one_div, Real.log_inv]; linarith)
    rw [Real.enorm_eq_ofReal_abs, abs_of_neg hlt]
    apply ENNReal.ofReal_le_ofReal
    have hthis : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
    linarith [hlogle, hthis]
  have hkey : ENNReal.ofReal (Real.log 2) * (MeasureTheory.volume.restrict B) A
      ≤ ∫⁻ t, ‖Real.log (R / ‖z - (t : ℂ)‖)‖ₑ ∂(MeasureTheory.volume.restrict B) := by
    calc ENNReal.ofReal (Real.log 2) * (MeasureTheory.volume.restrict B) A
        = ∫⁻ t, A.indicator (fun _ => ENNReal.ofReal (Real.log 2)) t
            ∂(MeasureTheory.volume.restrict B) :=
          (lintegral_indicator_const hAmeas (ENNReal.ofReal (Real.log 2))).symm
      _ ≤ ∫⁻ t, ‖Real.log (R / ‖z - (t : ℂ)‖)‖ₑ ∂(MeasureTheory.volume.restrict B) :=
          lintegral_mono (fun t => by
            by_cases ht : t ∈ A
            · rw [Set.indicator_of_mem ht]; exact hpt t ht
            · rw [Set.indicator_of_notMem ht]; exact bot_le)
  have hfinite : ENNReal.ofReal (Real.log 2) * (MeasureTheory.volume.restrict B) A < ⊤ :=
    lt_of_le_of_lt hkey h.2
  have hAfin : (MeasureTheory.volume.restrict B) A < ⊤ := by
    rcases ENNReal.mul_lt_top_iff.mp hfinite with ⟨-, hb⟩ | h0 | h0
    · exact hb
    · exact absurd h0 (ENNReal.ofReal_ne_zero_iff.mpr hlog2pos)
    · rw [h0]; exact bot_lt_top
  have h2fin : MeasureTheory.volume {t : ℝ | ‖z - (t : ℂ)‖ < 2 * R} < ⊤ := by
    have hsub : {t : ℝ | ‖z - (t : ℂ)‖ < 2 * R} ⊆ Set.Ioo (z.re - 2 * R) (z.re + 2 * R) := by
      intro t ht
      have h1 : |(z - (t : ℂ)).re| ≤ ‖z - (t : ℂ)‖ := Complex.abs_re_le_norm _
      rw [Complex.sub_re, Complex.ofReal_re] at h1
      have h2 : |z.re - t| < 2 * R := lt_of_le_of_lt h1 ht
      rw [abs_lt] at h2
      exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
    calc MeasureTheory.volume {t : ℝ | ‖z - (t : ℂ)‖ < 2 * R}
        ≤ MeasureTheory.volume (Set.Ioo (z.re - 2 * R) (z.re + 2 * R)) := measure_mono hsub
      _ = ENNReal.ofReal ((z.re + 2 * R) - (z.re - 2 * R)) := Real.volume_Ioo
      _ < ⊤ := ENNReal.ofReal_lt_top
  calc MeasureTheory.volume B
      = MeasureTheory.volume (A ∩ B ∪ Aᶜ ∩ B) := by
        rw [← Set.union_inter_distrib_right, Set.union_compl_self, Set.univ_inter]
    _ ≤ MeasureTheory.volume (A ∩ B) + MeasureTheory.volume (Aᶜ ∩ B) := measure_union_le _ _
    _ ≤ (MeasureTheory.volume.restrict B) A
          + MeasureTheory.volume {t : ℝ | ‖z - (t : ℂ)‖ < 2 * R} := by
        apply add_le_add
        · exact le_of_eq (Measure.restrict_apply hAmeas).symm
        · apply measure_mono
          intro t ht
          rw [Set.mem_inter_iff, Set.mem_compl_iff] at ht
          exact lt_of_not_ge (fun hc => ht.1 ((hAmem t).mpr hc))
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨hAfin, h2fin⟩

theorem rcPot_integrable_iff {B : Set ℝ} (hB : IsClosed B) {R : ℝ} (hR : 0 < R) {z w : ℂ}
    (hz : z ∉ Complex.ofReal '' B) (hw : w ∉ Complex.ofReal '' B) :
    (MeasureTheory.Integrable (fun t : ℝ => Real.log (R / ‖z - (t:ℂ)‖)) (MeasureTheory.volume.restrict B) ↔
     MeasureTheory.Integrable (fun t : ℝ => Real.log (R / ‖w - (t:ℂ)‖)) (MeasureTheory.volume.restrict B)) := by
  obtain ⟨δz, hδzpos, hzδ⟩ := rcPot_dist_pos hB hz
  obtain ⟨δw, hδwpos, hwδ⟩ := rcPot_dist_pos hB hw
  obtain ⟨M, hM⟩ := rcPot_log_diff_bounded hR hδzpos hδwpos hzδ hwδ
  have hmeas_z : Measurable (fun t : ℝ => Real.log (R / ‖z - (t:ℂ)‖)) :=
    Real.measurable_log.comp
      (measurable_const.div ((continuous_const.sub Complex.continuous_ofReal).norm.measurable))
  have hmeas_w : Measurable (fun t : ℝ => Real.log (R / ‖w - (t:ℂ)‖)) :=
    Real.measurable_log.comp
      (measurable_const.div ((continuous_const.sub Complex.continuous_ofReal).norm.measurable))
  have hdiff_int : MeasureTheory.volume B < ⊤ → MeasureTheory.Integrable
      (fun t : ℝ => Real.log (R / ‖z - (t:ℂ)‖) - Real.log (R / ‖w - (t:ℂ)‖))
      (MeasureTheory.volume.restrict B) := by
    intro hfin
    haveI : IsFiniteMeasure (MeasureTheory.volume.restrict B) :=
      ⟨by rwa [Measure.restrict_apply_univ]⟩
    refine MeasureTheory.Integrable.of_bound (hmeas_z.sub hmeas_w).aestronglyMeasurable M ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hB.measurableSet] with t ht
    rw [Real.norm_eq_abs]
    exact hM t ht
  constructor
  · intro hzint
    have hfin : MeasureTheory.volume B < ⊤ := rcPot_measure_lt_top_of_integrable hR hzint
    have hkey := hzint.sub (hdiff_int hfin)
    exact hkey.congr (Eventually.of_forall (fun t => by simp only [Pi.sub_apply]; ring))
  · intro hwint
    have hfin : MeasureTheory.volume B < ⊤ := rcPot_measure_lt_top_of_integrable hR hwint
    have hkey := hwint.add (hdiff_int hfin)
    exact hkey.congr (Eventually.of_forall (fun t => by simp only [Pi.add_apply]; ring))

end Work.TMComp.RealCartan
