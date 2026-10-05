import Mathlib

open MeasureTheory
open scoped ENNReal

namespace Work.RPB.B1

/-- The two-dimensional integral of `‖z‖⁻¹` over the closed disc of radius `M` centred at `0`:
`∫⁻_{B(0,M)} ‖z‖⁻¹ = 2πM`.  Computed in polar coordinates; for `M ≤ 0` both sides vanish. -/
private theorem lintegral_inv_norm_ball_aux (M : ℝ) :
    ∫⁻ z in Metric.ball (0 : ℂ) M, ENNReal.ofReal (‖z‖⁻¹) = ENNReal.ofReal (2 * Real.pi * M) := by
  classical
  have htarget : MeasurableSet (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi) :=
    measurableSet_Ioi.prod measurableSet_Ioo
  have hs : MeasurableSet (Set.Ioo (0:ℝ) M ×ˢ Set.Ioo (-Real.pi) Real.pi) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have hsub : Set.Ioo (0:ℝ) M ×ˢ Set.Ioo (-Real.pi) Real.pi ⊆
      Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi := by
    intro p hp
    rw [Set.mem_prod] at hp ⊢
    exact ⟨hp.1.1, hp.2⟩
  have key : ∀ p, p ∈ Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi →
      ENNReal.ofReal p.1 •
          (Metric.ball (0:ℂ) M).indicator (fun z => ENNReal.ofReal ‖z‖⁻¹)
            (Complex.polarCoord.symm p)
        = (Set.Ioo (0:ℝ) M ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator (fun _ => (1:ENNReal)) p := by
    intro p hp
    rw [Set.mem_prod, Set.mem_Ioi] at hp
    obtain ⟨hp1, hp2⟩ := hp
    have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
    have hmem : (Complex.polarCoord.symm p ∈ Metric.ball (0:ℂ) M) ↔ p.1 < M := by
      rw [Metric.mem_ball, dist_zero_right, hnorm]
    have hmem' : (p ∈ Set.Ioo (0:ℝ) M ×ˢ Set.Ioo (-Real.pi) Real.pi) ↔ p.1 < M := by
      rw [Set.mem_prod, Set.mem_Ioo, Set.mem_Ioo]
      constructor
      · intro h; exact h.1.2
      · intro h; exact ⟨⟨hp1, h⟩, hp2⟩
    rw [smul_eq_mul]
    by_cases hM : p.1 < M
    · rw [Set.indicator_of_mem (hmem.mpr hM), Set.indicator_of_mem (hmem'.mpr hM), hnorm]
      rw [← ENNReal.ofReal_mul (le_of_lt hp1), mul_inv_cancel₀ hp1.ne', ENNReal.ofReal_one]
    · rw [Set.indicator_of_notMem (fun h => hM (hmem.mp h)),
          Set.indicator_of_notMem (fun h => hM (hmem'.mp h)), mul_zero]
  rw [← MeasureTheory.lintegral_indicator measurableSet_ball]
  rw [← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
  rw [MeasureTheory.setLIntegral_congr_fun htarget key]
  rw [MeasureTheory.setLIntegral_indicator hs (fun _ => (1:ENNReal))]
  rw [Set.inter_eq_left.mpr hsub, MeasureTheory.setLIntegral_one]
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ, MeasureTheory.Measure.prod_prod,
      Real.volume_Ioo, Real.volume_Ioo]
  rw [sub_zero, show Real.pi - -Real.pi = 2 * Real.pi by ring]
  rw [ENNReal.ofReal_mul (show (0:ℝ) ≤ 2 * Real.pi by positivity)]
  exact mul_comm _ _

/-- For a point `a` strictly inside the disc of radius `R`, the integral of `‖a - q‖⁻¹` over the
disc is at most `4πR` (the sharp value is `2πR`).  Obtained from the previous computation after
enlarging `B(0,R)` to `B(a,2R)` and translating. -/
private theorem lintegral_inv_norm_sub_le_aux (a : ℂ) {R : ℝ} (hR : ‖a‖ < R) :
    ∫⁻ q in Metric.ball (0:ℂ) R, ENNReal.ofReal (‖a - q‖⁻¹) ≤ ENNReal.ofReal (4 * Real.pi * R) := by
  have hsub : Metric.ball (0:ℂ) R ⊆ Metric.ball a (2*R) := by
    intro q hq
    rw [Metric.mem_ball, dist_zero_right] at hq
    rw [Metric.mem_ball, dist_eq_norm]
    have h1 : ‖q - a‖ ≤ ‖q‖ + ‖a‖ := by
      calc ‖q - a‖ = ‖q + (-a)‖ := by ring_nf
        _ ≤ ‖q‖ + ‖-a‖ := norm_add_le _ _
        _ = ‖q‖ + ‖a‖ := by rw [norm_neg]
    linarith
  have htrans : ∫⁻ q in Metric.ball a (2*R), ENNReal.ofReal (‖a - q‖⁻¹)
      = ∫⁻ w in Metric.ball (0:ℂ) (2*R), ENNReal.ofReal (‖w‖⁻¹) := by
    rw [← MeasureTheory.lintegral_indicator measurableSet_ball,
        ← MeasureTheory.lintegral_indicator measurableSet_ball]
    rw [← MeasureTheory.lintegral_add_right_eq_self
          ((Metric.ball a (2*R)).indicator (fun q => ENNReal.ofReal (‖a - q‖⁻¹))) a]
    apply MeasureTheory.lintegral_congr
    intro x
    by_cases hx : x ∈ Metric.ball (0:ℂ) (2*R)
    · have hxa : x + a ∈ Metric.ball a (2*R) := by
        rw [Metric.mem_ball, dist_zero_right] at hx
        rw [Metric.mem_ball, dist_eq_norm]
        rwa [show x + a - a = x by ring]
      rw [Set.indicator_of_mem hxa, Set.indicator_of_mem hx]
      congr 1
      rw [show a - (x + a) = -x by ring, norm_neg]
    · have hxa : x + a ∉ Metric.ball a (2*R) := by
        intro h
        apply hx
        rw [Metric.mem_ball, dist_eq_norm] at h
        rw [Metric.mem_ball, dist_zero_right]
        rwa [show x + a - a = x by ring] at h
      rw [Set.indicator_of_notMem hxa, Set.indicator_of_notMem hx]
  calc ∫⁻ q in Metric.ball (0:ℂ) R, ENNReal.ofReal (‖a - q‖⁻¹)
      ≤ ∫⁻ q in Metric.ball a (2*R), ENNReal.ofReal (‖a - q‖⁻¹) := lintegral_mono_set hsub
    _ = ∫⁻ w in Metric.ball (0:ℂ) (2*R), ENNReal.ofReal (‖w‖⁻¹) := htrans
    _ = ENNReal.ofReal (2 * Real.pi * (2*R)) := lintegral_inv_norm_ball_aux (2*R)
    _ = ENNReal.ofReal (4 * Real.pi * R) := by congr 1; ring

/-- **Kernel swap.**  For a `C¹` curve `u : ℝ → ℂ` that stays strictly inside the disc of radius
`R`, the two iterated integrals of the Cauchy kernel `(t, q) ↦ Im (u' t / (u t - q))` over
`(0, 2π) × B(0,R)` agree.  The kernel is integrable on the product: the singularity along the
graph of `u` is codimension two, and on each slice `q ↦ ‖u t - q‖⁻¹` has `L¹`-norm at most
`4πR`, while `t ↦ ‖u' t‖` is bounded on the compact interval. -/
theorem kernelSwap (u : ℝ → ℂ) (hu : ContDiff ℝ 1 u) {R : ℝ} (hR : ∀ t, ‖u t‖ < R) :
    ∫ q in Metric.ball (0 : ℂ) R, ∫ t in (0 : ℝ)..(2 * Real.pi), (deriv u t / (u t - q)).im
      = ∫ t in (0 : ℝ)..(2 * Real.pi),
          ∫ q in Metric.ball (0 : ℂ) R, (deriv u t / (u t - q)).im := by
  have h2pi : (0:ℝ) ≤ 2 * Real.pi := by positivity
  have hcont : Continuous (deriv u) := hu.continuous_deriv_one
  have hderiv_meas : Measurable (deriv u) := hcont.measurable
  have hu_meas : Measurable u := hu.continuous.measurable
  -- Measurability of the kernel on the product of the two restricted Lebesgue measures.
  have hmeas : AEStronglyMeasurable
      (Function.uncurry (fun t q => (deriv u t / (u t - q)).im))
      ((volume.restrict (Set.Ioc (0:ℝ) (2*Real.pi))).prod
        (volume.restrict (Metric.ball (0:ℂ) R))) := by
    have hm : Measurable (fun p : ℝ × ℂ => deriv u p.1 / (u p.1 - p.2)) :=
      (hderiv_meas.comp measurable_fst).div ((hu_meas.comp measurable_fst).sub measurable_snd)
    exact (Complex.measurable_im.comp hm).aestronglyMeasurable
  -- A dominating function for the (extended) norm of the kernel.
  set G : ℝ × ℂ → ℝ≥0∞ := fun p => ENNReal.ofReal (‖deriv u p.1‖ * ‖u p.1 - p.2‖⁻¹) with hG
  have hG_meas : Measurable G := by
    have h1 : Measurable (fun p : ℝ × ℂ => ‖deriv u p.1‖) :=
      hderiv_meas.norm.comp measurable_fst
    have h2 : Measurable (fun p : ℝ × ℂ => ‖u p.1 - p.2‖⁻¹) :=
      ((hu_meas.comp measurable_fst).sub measurable_snd).norm.inv
    exact ENNReal.measurable_ofReal.comp (h1.mul h2)
  have hle : ∀ p : ℝ × ℂ,
      ENNReal.ofReal ‖Function.uncurry (fun t q => (deriv u t / (u t - q)).im) p‖ ≤ G p := by
    intro p
    apply ENNReal.ofReal_le_ofReal
    calc ‖Function.uncurry (fun t q => (deriv u t / (u t - q)).im) p‖
        = |(deriv u p.1 / (u p.1 - p.2)).im| := by
          simp only [Function.uncurry, Real.norm_eq_abs]
      _ ≤ ‖deriv u p.1 / (u p.1 - p.2)‖ := Complex.abs_im_le_norm _
      _ = ‖deriv u p.1‖ / ‖u p.1 - p.2‖ := norm_div _ _
      _ = ‖deriv u p.1‖ * ‖u p.1 - p.2‖⁻¹ := by rw [div_eq_mul_inv]
  have hq_meas : ∀ t : ℝ, Measurable (fun q : ℂ => ENNReal.ofReal (‖u t - q‖⁻¹)) := by
    intro t
    exact ENNReal.measurable_ofReal.comp ((continuous_const.sub continuous_id).norm.measurable.inv)
  -- The `q`-slice of the dominating function is bounded uniformly in `t`.
  have hinner : ∀ t : ℝ, ∫⁻ q, G (t, q) ∂(volume.restrict (Metric.ball (0:ℂ) R))
      ≤ ENNReal.ofReal ‖deriv u t‖ * ENNReal.ofReal (4 * Real.pi * R) := by
    intro t
    have hsplit : ∫⁻ q, G (t, q) ∂(volume.restrict (Metric.ball (0:ℂ) R))
        = ENNReal.ofReal ‖deriv u t‖ *
            ∫⁻ q, ENNReal.ofReal (‖u t - q‖⁻¹) ∂(volume.restrict (Metric.ball (0:ℂ) R)) := by
      rw [← lintegral_const_mul (ENNReal.ofReal ‖deriv u t‖) (hq_meas t)]
      apply lintegral_congr
      intro q
      simp only [hG]
      rw [ENNReal.ofReal_mul (norm_nonneg _)]
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left (lintegral_inv_norm_sub_le_aux (u t) (hR t)) (by positivity)
  have hderiv_int : Integrable (deriv u) (volume.restrict (Set.Ioc (0:ℝ) (2*Real.pi))) := by
    rw [← Set.uIoc_of_le h2pi]
    exact intervalIntegrable_iff.mp (hcont.intervalIntegrable 0 (2*Real.pi))
  have hJfin :
      ∫⁻ t, ENNReal.ofReal ‖deriv u t‖ ∂(volume.restrict (Set.Ioc (0:ℝ) (2*Real.pi))) < ⊤ :=
    (MeasureTheory.hasFiniteIntegral_iff_norm
        (μ := volume.restrict (Set.Ioc (0:ℝ) (2*Real.pi))) (deriv u)).mp
      hderiv_int.hasFiniteIntegral
  have hd_meas : Measurable (fun t : ℝ => ENNReal.ofReal ‖deriv u t‖) :=
    ENNReal.measurable_ofReal.comp hderiv_meas.norm
  -- Integrability of the kernel on the product.
  have hint : Integrable (Function.uncurry (fun t q => (deriv u t / (u t - q)).im))
      ((volume.restrict (Set.Ioc (0:ℝ) (2*Real.pi))).prod
        (volume.restrict (Metric.ball (0:ℂ) R))) := by
    refine ⟨hmeas, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_norm]
    calc ∫⁻ p, ENNReal.ofReal ‖Function.uncurry (fun t q => (deriv u t / (u t - q)).im) p‖
            ∂((volume.restrict (Set.Ioc (0:ℝ) (2*Real.pi))).prod
              (volume.restrict (Metric.ball (0:ℂ) R)))
        ≤ ∫⁻ p, G p ∂((volume.restrict (Set.Ioc (0:ℝ) (2*Real.pi))).prod
              (volume.restrict (Metric.ball (0:ℂ) R))) := lintegral_mono hle
      _ = ∫⁻ t, ∫⁻ q, G (t, q) ∂(volume.restrict (Metric.ball (0:ℂ) R))
              ∂(volume.restrict (Set.Ioc (0:ℝ) (2*Real.pi))) := by
          exact MeasureTheory.lintegral_prod G hG_meas.aemeasurable
      _ ≤ ∫⁻ t, ENNReal.ofReal ‖deriv u t‖ * ENNReal.ofReal (4 * Real.pi * R)
              ∂(volume.restrict (Set.Ioc (0:ℝ) (2*Real.pi))) := lintegral_mono hinner
      _ = ENNReal.ofReal (4 * Real.pi * R) *
            ∫⁻ t, ENNReal.ofReal ‖deriv u t‖
              ∂(volume.restrict (Set.Ioc (0:ℝ) (2*Real.pi))) := by
          rw [← lintegral_const_mul (ENNReal.ofReal (4 * Real.pi * R)) hd_meas]
          apply lintegral_congr
          intro t
          rw [mul_comm]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hJfin
  have h_int : Integrable (Function.uncurry (fun t q => (deriv u t / (u t - q)).im))
      ((volume.restrict (Set.uIoc (0:ℝ) (2*Real.pi))).prod
        (volume.restrict (Metric.ball (0:ℂ) R))) := by
    rw [Set.uIoc_of_le h2pi]
    exact hint
  exact (MeasureTheory.intervalIntegral_integral_swap
    (μ := volume.restrict (Metric.ball (0:ℂ) R)) h_int).symm

end Work.RPB.B1
