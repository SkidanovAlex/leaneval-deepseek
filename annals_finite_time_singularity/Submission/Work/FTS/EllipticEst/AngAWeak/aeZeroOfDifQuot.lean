import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngAWeak

/-- If `M₀` vanishes a.e. on `(0,∞)` and the (left) difference quotients of `M₀` converge
pointwise on `(0,∞)` to `M₁`, then `M₁` vanishes a.e. on `(0,∞)`.

Indeed, if `M₁ z ≠ 0` for some `z > 0`, the convergence of the difference quotient at `z`
forces `M₀` to be nonzero on a whole left neighbourhood of `z`, i.e. on a set of positive
measure, contradicting the a.e. vanishing of `M₀`. -/
theorem aeZeroOfDifQuot {M₀ M₁ : ℝ → ℝ}
    (hM : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), M₀ z = 0)
    (hT : ∀ z : ℝ, 0 < z → Filter.Tendsto (fun hh : ℝ => (M₀ z - M₀ (z - hh)) / hh)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (M₁ z))) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), M₁ z = 0 := by
  rw [MeasureTheory.ae_iff] at hM ⊢
  rw [MeasureTheory.Measure.restrict_apply' measurableSet_Ioi] at hM ⊢
  refine MeasureTheory.measure_mono_null ?_ hM
  rintro w ⟨hw1, hw2⟩
  have hwpos : (0 : ℝ) < w := hw2
  refine ⟨?_, hw2⟩
  intro hM0
  have hLpos : 0 < |M₁ w| := abs_pos.mpr hw1
  obtain ⟨δ, hδpos, hδ⟩ :=
    (Metric.tendsto_nhdsWithin_nhds.mp (hT w hw2)) (|M₁ w| / 2) (by linarith)
  let h0 := min δ (w / 2)
  have h0leδ : h0 ≤ δ := min_le_left δ (w / 2)
  have h0lew : h0 ≤ w / 2 := min_le_right δ (w / 2)
  have h0pos : 0 < h0 := lt_min hδpos (by linarith)
  have hsub : Set.Ioo (w - h0) w ⊆ {v | M₀ v ≠ 0} ∩ Set.Ioi 0 := by
    rintro v ⟨hv1, hv2⟩
    have hvpos : 0 < v := by linarith
    have hdpos : 0 < w - v := by linarith
    have hdlt : w - v < δ := by linarith
    have hdist : dist (w - v) 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hdpos]; exact hdlt
    have hkey := hδ hdpos hdist
    have hzv : w - (w - v) = v := by ring
    rw [hzv, hM0, zero_sub] at hkey
    refine ⟨?_, hvpos⟩
    intro hMv
    rw [hMv] at hkey
    simp only [neg_zero, zero_div, dist_zero_left, Real.norm_eq_abs] at hkey
    linarith
  have hzero : MeasureTheory.volume (Set.Ioo (w - h0) w) = 0 :=
    MeasureTheory.measure_mono_null hsub hM
  rw [Real.volume_Ioo] at hzero
  have hz0 : w - (w - h0) = h0 := by ring
  rw [hz0] at hzero
  exact absurd hzero (ne_of_gt (ENNReal.ofReal_pos.mpr h0pos))

end Work.FTS.EllipticEst.AngAWeak
