import Mathlib
import Submission.Work.Beltrami.dbarW_cauchyT_defs

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Work.Beltrami

/-- The radial cutoff kernel is measurable (it is even continuous). -/
lemma measurable_cutK (ε : ℝ) : Measurable (cutK ε) := by
  unfold cutK
  refine Measurable.mul ?_ measurable_inv
  exact Complex.continuous_ofReal.measurable.comp
    (((differentiable_cutProfile ε).continuous.comp (continuous_norm.pow 2)).measurable)

/-- The (real) cutoff profile, viewed in `ℂ`, has norm at most `1`. -/
lemma norm_ofReal_cutProfile_le_one (ε : ℝ) (u : ℂ) :
    ‖(cutProfile ε (‖u‖^2) : ℂ)‖ ≤ 1 := by
  have h : ‖((cutProfile ε (‖u‖^2) : ℝ) : ℂ)‖ = |cutProfile ε (‖u‖^2)| := by
    rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs]
  rw [h, abs_le]
  refine ⟨?_, ?_⟩
  · simp only [cutProfile]; linarith [Real.smoothTransition.nonneg (‖u‖^2/ε^2 - 1)]
  · simp only [cutProfile]; exact Real.smoothTransition.le_one _

/-- The cutoff kernel is dominated by the Cauchy kernel `u ↦ u⁻¹`. -/
lemma norm_cutK_le (ε : ℝ) (u : ℂ) : ‖cutK ε u‖ ≤ ‖u⁻¹‖ := by
  rw [cutK, norm_mul]
  calc ‖(cutProfile ε (‖u‖^2) : ℂ)‖ * ‖u⁻¹‖ ≤ 1 * ‖u⁻¹‖ :=
        mul_le_mul_of_nonneg_right (norm_ofReal_cutProfile_le_one ε u) (norm_nonneg _)
    _ = ‖u⁻¹‖ := one_mul _

/-- For a fixed nonzero `u` the smooth cutoff is eventually `1` along `ε → 0⁺`:
the support of the cutoff grows to fill the whole plane, it is `1` as soon as
`ε² ≤ ‖u‖²/2`. -/
lemma cutProfile_eventually_one (u : ℂ) (hu : u ≠ 0) :
    ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0), cutProfile ε (‖u‖^2) = 1 := by
  have hs : 0 < ‖u‖^2 := pow_pos (norm_pos_iff.mpr hu) 2
  set δ := Real.sqrt (‖u‖^2 / 2) with hδdef
  have hδ : 0 < δ := Real.sqrt_pos.mpr (by positivity)
  have hmem : Set.Ioo 0 δ ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) :=
    Filter.inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hδ))
  refine Filter.mem_of_superset hmem ?_
  intro ε hε
  rw [Set.mem_Ioo] at hε
  obtain ⟨hεpos, hεδ⟩ := hε
  show Real.smoothTransition (‖u‖^2 / ε^2 - 1) = 1
  rw [Real.smoothTransition.eq_one_iff_one_le]
  have hδ2 : δ ^ 2 = ‖u‖^2 / 2 := Real.sq_sqrt (by positivity)
  have hε2 : ε ^ 2 < ‖u‖^2 / 2 := by
    nlinarith [hεpos, hεδ, hδ2, Real.sqrt_nonneg (‖u‖^2/2), sq_nonneg ε, hs]
  have h2 : 2 ≤ ‖u‖^2 / ε^2 := by
    rw [le_div_iff₀ (pow_pos hεpos 2)]
    nlinarith [hε2]
  linarith

/-- `u ↦ u⁻¹` is locally integrable on `ℂ`; consequently its product with a
continuous compactly supported function is integrable. -/
lemma integrable_mul_inv (g : ℂ → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun u => g u * u⁻¹) volume := by
  have hloc : LocallyIntegrable (fun u : ℂ => u⁻¹) volume := by
    refine MeasureTheory.locallyIntegrable_of_norm_le_rpow (E := ℂ) (F := ℂ) (C := 1) (α := 1)
      ?_ ?_ ?_ ?_
    · rw [Complex.finrank_real_complex]; norm_num
    · rw [Complex.finrank_real_complex]; norm_num
    · filter_upwards with x
      rw [one_mul, norm_inv, Real.rpow_neg_one]
    · exact measurable_inv.aestronglyMeasurable
  have := hloc.integrable_smul_left_of_hasCompactSupport hg hgc
  simpa only [smul_eq_mul] using this

/-- The cutoff kernel `cutK ε` converges weakly to the Cauchy kernel `u ↦ u⁻¹`:
for every continuous compactly supported `g`,
`∫ g u * cutK ε u → ∫ g u * u⁻¹` as `ε → 0⁺`. -/
theorem tendsto_cutK_mul (g : ℂ → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g) :
    Filter.Tendsto (fun ε : ℝ => ∫ u, g u * cutK ε u ∂volume)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ u, g u * u⁻¹ ∂volume)) := by
  have hInt := integrable_mul_inv g hg hgc
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun u => ‖g u * u⁻¹‖) ?hmeas ?hbound hInt.norm ?hlim
  · -- measurability of the integrands
    filter_upwards with ε
    exact (hg.measurable.mul (measurable_cutK ε)).aestronglyMeasurable
  · -- uniform domination by ‖g u * u⁻¹‖
    filter_upwards with ε
    filter_upwards with u
    calc ‖g u * cutK ε u‖ = ‖g u‖ * ‖cutK ε u‖ := norm_mul _ _
      _ ≤ ‖g u‖ * ‖u⁻¹‖ := mul_le_mul_of_nonneg_left (norm_cutK_le ε u) (norm_nonneg _)
      _ = ‖g u * u⁻¹‖ := (norm_mul _ _).symm
  · -- pointwise (a.e.) convergence: the cutoff becomes `1` around every `u ≠ 0`
    filter_upwards with u
    by_cases hu : u = 0
    · subst hu
      have h0 : (fun ε : ℝ => g 0 * cutK ε 0) = fun _ => (0 : ℂ) := by
        funext ε; simp [cutK]
      rw [h0, show g 0 * (0:ℂ)⁻¹ = 0 from by simp]
      exact tendsto_const_nhds
    · have hev : (fun ε : ℝ => g u * cutK ε u)
          =ᶠ[nhdsWithin 0 (Set.Ioi 0)] (fun _ => g u * u⁻¹) := by
        filter_upwards [cutProfile_eventually_one u hu] with ε hε
        simp [cutK, hε]
      exact Filter.Tendsto.congr' hev.symm tendsto_const_nhds

end Work.Beltrami
