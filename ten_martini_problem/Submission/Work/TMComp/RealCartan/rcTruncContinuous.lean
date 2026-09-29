import Mathlib

namespace Work.TMComp.RealCartan

open MeasureTheory Filter Topology Set

theorem rcTruncContinuous {B : Set ℝ} (hB : Bornology.IsBounded B) {R : ℝ} (hR : 0 < R)
    {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun z : ℂ => ∫ t in B, Real.log (R / max ‖z - (t : ℂ)‖ ε)) := by
  rw [continuous_iff_continuousAt]
  intro z₀
  obtain ⟨r, hr, hBr⟩ := hB.subset_ball_lt 0 (0 : ℝ)
  have hrt : ∀ t ∈ B, |t| ≤ r := by
    intro t ht
    have h1 : t ∈ Metric.ball (0 : ℝ) r := hBr ht
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at h1
    exact le_of_lt h1
  set K : ℝ := ‖z₀‖ + 1 + r with hK
  set C : ℝ := max |Real.log (R / max K ε)| |Real.log (R / ε)| with hC
  have hbnd : ∀ x : ℂ, ‖x - z₀‖ < 1 → ∀ t ∈ B,
      ‖Real.log (R / max ‖x - (t : ℂ)‖ ε)‖ ≤ C := by
    intro x hx t ht
    have hnt : ‖(t : ℂ)‖ = |t| := by rw [Complex.norm_real, Real.norm_eq_abs]
    have hdt : ‖x - (t : ℂ)‖ ≤ K := by
      have hsplit : x - (t : ℂ) = (x - z₀) + (z₀ - (t : ℂ)) := by ring
      rw [hsplit]
      calc ‖(x - z₀) + (z₀ - (t : ℂ))‖ ≤ ‖x - z₀‖ + ‖z₀ - (t : ℂ)‖ := norm_add_le _ _
        _ ≤ 1 + (‖z₀‖ + ‖(t : ℂ)‖) := add_le_add (le_of_lt hx) (norm_sub_le _ _)
        _ = ‖z₀‖ + |t| + 1 := by rw [hnt]; ring
        _ ≤ ‖z₀‖ + r + 1 := by linarith [hrt t ht]
        _ = K := by rw [hK]; ring
    have hmaxd : 0 < max ‖x - (t : ℂ)‖ ε := lt_of_lt_of_le hε (le_max_right _ _)
    have hle1 : Real.log (R / max K ε) ≤ Real.log (R / max ‖x - (t : ℂ)‖ ε) :=
      Real.log_le_log (div_pos hR (lt_of_lt_of_le hε (le_max_right _ _)))
        (div_le_div_of_nonneg_left hR.le hmaxd (max_le_max hdt le_rfl))
    have hle2 : Real.log (R / max ‖x - (t : ℂ)‖ ε) ≤ Real.log (R / ε) :=
      Real.log_le_log (div_pos hR hmaxd) (div_le_div_of_nonneg_left hR.le hε (le_max_right _ _))
    rw [Real.norm_eq_abs, hC]
    refine abs_le.mpr ⟨?_, ?_⟩
    · exact le_trans (neg_le_neg (le_max_left _ _)) (le_trans (neg_abs_le _) hle1)
    · exact le_trans hle2 (le_trans (le_abs_self _) (le_max_right _ _))
  have hcont_zt : ∀ t : ℝ, Continuous (fun z : ℂ => Real.log (R / max ‖z - (t : ℂ)‖ ε)) := by
    intro t
    exact (Continuous.div continuous_const
      ((continuous_id.sub continuous_const).norm.max continuous_const)
      (fun z => ne_of_gt (lt_of_lt_of_le hε (le_max_right _ _)))).log
      (fun z => ne_of_gt (div_pos hR (lt_of_lt_of_le hε (le_max_right _ _))))
  have hcont_xt : ∀ x : ℂ, Continuous (fun t : ℝ => Real.log (R / max ‖x - (t : ℂ)‖ ε)) := by
    intro x
    exact (Continuous.div continuous_const
      ((continuous_const.sub Complex.continuous_ofReal).norm.max continuous_const)
      (fun t => ne_of_gt (lt_of_lt_of_le hε (le_max_right _ _)))).log
      (fun t => ne_of_gt (div_pos hR (lt_of_lt_of_le hε (le_max_right _ _))))
  have hbound_ae : ∀ᶠ x in 𝓝 z₀, ∀ᵐ t : ℝ ∂(volume.restrict B),
      ‖Real.log (R / max ‖x - (t : ℂ)‖ ε)‖ ≤ C := by
    filter_upwards [Metric.ball_mem_nhds z₀ (by norm_num : (0 : ℝ) < 1)] with x hx
    have hx' : ‖x - z₀‖ < 1 := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hx
    rw [MeasureTheory.ae_iff]
    have hmeas : MeasurableSet {t : ℝ | ¬ ‖Real.log (R / max ‖x - (t : ℂ)‖ ε)‖ ≤ C} := by
      rw [show {t : ℝ | ¬ ‖Real.log (R / max ‖x - (t : ℂ)‖ ε)‖ ≤ C}
            = (fun t : ℝ => ‖Real.log (R / max ‖x - (t : ℂ)‖ ε)‖) ⁻¹' Set.Ioi C from by
          ext t; simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ioi]; exact not_le]
      exact measurableSet_Ioi.preimage ((hcont_xt x).norm).measurable
    have hbad : {t : ℝ | ¬ ‖Real.log (R / max ‖x - (t : ℂ)‖ ε)‖ ≤ C} ∩ B = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro t ht
      obtain ⟨h1, h2⟩ := ht
      exact absurd (hbnd x hx' t h2) h1
    rw [Measure.restrict_apply hmeas, hbad, measure_empty]
  have hadapt : ∀ᶠ x in 𝓝 z₀, AEStronglyMeasurable
      (fun t : ℝ => Real.log (R / max ‖x - (t : ℂ)‖ ε)) (volume.restrict B) :=
    Eventually.of_forall (fun x => (hcont_xt x).aestronglyMeasurable)
  have hint : Integrable (fun _ : ℝ => C) (volume.restrict B) :=
    integrable_const_iff.mpr (Or.inr (isFiniteMeasure_restrict.mpr (ne_of_lt hB.measure_lt_top)))
  exact continuousAt_of_dominated hadapt hbound_ae hint
    (Eventually.of_forall (fun t => (hcont_zt t).continuousAt))

end Work.TMComp.RealCartan
