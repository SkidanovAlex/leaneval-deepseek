import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open MeasureTheory Set Filter

/-- The box `∏ᵢ [-δ/2, δ/2]` of side `δ` around the origin is contained in the metric
ball of radius `η` as soon as `δ/2 < η`.  (The metric on `Fin m → ℝ` is the sup metric, so
the distance to the origin is bounded by the largest coordinate, which is `≤ δ/2`.) -/
lemma vaalerAvgBox_box_subset_ball {m : ℕ} {δ η : ℝ} (hδ : 0 < δ) (hδη : δ/2 < η) :
    Set.pi Set.univ (fun _ : Fin m => Set.Icc (-(δ/2)) (δ/2)) ⊆ Metric.ball (0 : Fin m → ℝ) η := by
  intro y hy
  rw [Metric.mem_ball]
  have h2 : (0:ℝ) ≤ δ/2 := by linarith
  have hle : dist y (0 : Fin m → ℝ) ≤ δ/2 := by
    rw [dist_pi_le_iff h2]
    intro i
    have hi := Set.mem_univ_pi.mp hy i
    simp only [Pi.zero_apply]
    rw [Real.dist_eq, sub_zero, abs_le]
    exact ⟨(Set.mem_Icc.mp hi).1, (Set.mem_Icc.mp hi).2⟩
  linarith

/-- Averaging estimate: if `F` is measurable and `‖F y - F 0‖ ≤ ε` on the box of side `δ`
(with `δ > 0`), then the average of `F` over the box differs from `F 0` by at most `ε`.
The volume of the box is `δ ^ m`, which cancels the normalising factor `1 / δ ^ m`. -/
lemma vaalerAvgBox_bound {m : ℕ} {F : (Fin m → ℝ) → ℝ} (hm : Measurable F) {δ ε : ℝ}
    (hδ : 0 < δ)
    (hbound : ∀ y ∈ Set.pi Set.univ (fun _ : Fin m => Set.Icc (-(δ/2)) (δ/2)), ‖F y - F 0‖ ≤ ε) :
    ‖(1/δ^m) * (∫ y in Set.pi Set.univ (fun _ : Fin m => Set.Icc (-(δ/2)) (δ/2)), F y) - F 0‖ ≤ ε := by
  set s : Set (Fin m → ℝ) := Set.pi Set.univ (fun _ : Fin m => Set.Icc (-(δ/2)) (δ/2)) with hs
  have hmeas_s : MeasurableSet s := by
    rw [hs]
    exact MeasurableSet.univ_pi (fun _ => isClosed_Icc.measurableSet)
  have hvol : volume s = ENNReal.ofReal (δ^m) := by
    rw [hs, MeasureTheory.volume_pi, MeasureTheory.Measure.pi_pi]
    simp only [Real.volume_Icc]
    have h2 : (∏ x : Fin m, ENNReal.ofReal (δ / 2 - -(δ / 2))) = ∏ _x : Fin m, ENNReal.ofReal δ := by
      apply Finset.prod_congr rfl
      intro i _
      congr 1
      ring
    rw [h2, Fin.prod_const, ← ENNReal.ofReal_pow (le_of_lt hδ)]
  have hvol_real : volume.real s = δ^m := by
    rw [MeasureTheory.Measure.real_def, hvol, ENNReal.toReal_ofReal (pow_nonneg (le_of_lt hδ) m)]
  have hs_top : volume s < ⊤ := by rw [hvol]; exact ENNReal.ofReal_lt_top
  have hs_ne : volume s ≠ ⊤ := ne_of_lt hs_top
  have hFasm : AEStronglyMeasurable F (volume.restrict s) :=
    hm.aestronglyMeasurable.mono_measure Measure.restrict_le_self
  have hIntF : IntegrableOn F s volume :=
    IntegrableOn.of_bound hs_top hFasm (‖F 0‖ + ε) (by
      rw [MeasureTheory.ae_restrict_iff' hmeas_s]
      refine Filter.Eventually.of_forall (fun y hy => ?_)
      have hyb := hbound y hy
      calc ‖F y‖ = ‖(F y - F 0) + F 0‖ := by ring_nf
        _ ≤ ‖F y - F 0‖ + ‖F 0‖ := norm_add_le _ _
        _ ≤ ε + ‖F 0‖ := by linarith
        _ = ‖F 0‖ + ε := by ring)
  have hIntC : IntegrableOn (fun _ : Fin m → ℝ => F 0) s volume :=
    integrableOn_const hs_ne
  have hsub_int : (∫ y in s, (F y - F 0)) = (∫ y in s, F y) - (∫ y in s, (F 0)) :=
    integral_sub hIntF hIntC
  have hconst : (∫ y in s, (F 0)) = volume.real s * F 0 := by
    rw [MeasureTheory.setIntegral_const, smul_eq_mul]
  have hnorm : ‖∫ y in s, (F y - F 0)‖ ≤ ε * volume.real s :=
    MeasureTheory.norm_setIntegral_le_of_norm_le_const hs_top (fun y hy => hbound y hy)
  have hkey : (1/δ^m) * (∫ y in s, F y) - F 0 = (1/δ^m) * (∫ y in s, (F y - F 0)) := by
    rw [hsub_int, hconst, hvol_real]
    set A : ℝ := ∫ y in s, F y with hA
    have hδm : δ^m ≠ 0 := pow_ne_zero m (ne_of_gt hδ)
    field_simp
  calc ‖(1/δ^m) * (∫ y in s, F y) - F 0‖
      = ‖(1/δ^m) * (∫ y in s, (F y - F 0))‖ := by rw [hkey]
    _ = (1/δ^m) * ‖∫ y in s, (F y - F 0)‖ := by
          rw [norm_mul]
          congr 1
          rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    _ ≤ (1/δ^m) * (ε * volume.real s) := by
          apply mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = ε := by
          rw [hvol_real]
          field_simp

theorem vaalerAvgBox {m : ℕ} (F : (Fin m → ℝ) → ℝ)
    (hF : ContinuousAt F 0) (hm : Measurable F) :
    Filter.Tendsto
      (fun δ : ℝ => (1/δ^m) * ∫ y in Set.pi Set.univ (fun _ : Fin m => Set.Icc (-(δ/2)) (δ/2)), F y)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (F 0)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hcont : ∀ᶠ y in nhds (0 : Fin m → ℝ), dist (F y) (F 0) < ε/2 :=
    (Metric.tendsto_nhds.mp hF) (ε/2) (by linarith)
  obtain ⟨η, hηpos, hηsub⟩ := Metric.mem_nhds_iff.mp hcont
  have hev : ∀ᶠ δ in nhdsWithin (0:ℝ) (Set.Ioi 0), δ ∈ Set.Ioo (0:ℝ) (2*η) := by
    rw [Set.Ioo]
    exact inter_mem self_mem_nhdsWithin
      (nhdsWithin_le_nhds (Iio_mem_nhds (by linarith : (0:ℝ) < 2*η)))
  refine Filter.Eventually.mono hev ?_
  intro δ hδ
  obtain ⟨hδpos, hδlt⟩ := hδ
  have hδη : δ/2 < η := by linarith
  have hsub := vaalerAvgBox_box_subset_ball (m := m) hδpos hδη
  have hbound : ∀ y ∈ Set.pi Set.univ (fun _ : Fin m => Set.Icc (-(δ/2)) (δ/2)),
      ‖F y - F 0‖ ≤ ε/2 := by
    intro y hy
    have h1 : dist (F y) (F 0) < ε/2 := hηsub (hsub hy)
    rw [Real.dist_eq] at h1
    rw [Real.norm_eq_abs]
    linarith
  have hmain := vaalerAvgBox_bound hm hδpos hbound
  rw [Real.dist_eq]
  rw [Real.norm_eq_abs] at hmain
  linarith

end Work.BW
