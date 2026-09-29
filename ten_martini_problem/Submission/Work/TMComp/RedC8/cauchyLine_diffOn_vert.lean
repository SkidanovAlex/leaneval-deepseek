import Mathlib

open MeasureTheory intervalIntegral Set Filter
open scoped Interval Topology

namespace Work.TMComp.RedC8

/-- The Cauchy-type integral `z ↦ ∫_c^d (a + i·t - z)⁻¹ · F t dt` is holomorphic in `z`
off the vertical line `{z | z.re = a}`, where the integrand's singularity lies.  The proof is
differentiation under the integral sign: for `z₀` with `z₀.re ≠ a` the singular set of the
integrand stays at distance `δ/2 = |z₀.re - a|/2` from a small ball around `z₀`, which bounds
both the integrand and its `z`-derivative. -/
theorem cauchyLine_diffOn_vert {a c d M : ℝ} {F : ℝ → ℂ}
    (hfm : MeasureTheory.AEStronglyMeasurable F (MeasureTheory.volume.restrict (Set.uIoc c d)))
    (hfb : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.uIoc c d)), ‖F t‖ ≤ M) :
    DifferentiableOn ℂ
      (fun z => ∫ t : ℝ in c..d, ((a : ℂ) + (t : ℂ) * Complex.I - z)⁻¹ * F t)
      {z : ℂ | z.re ≠ a} := by
  intro z₀ hz₀
  let δ : ℝ := |z₀.re - a|
  have hδeq : δ = |z₀.re - a| := rfl
  have hδpos : 0 < δ := by
    rw [hδeq, abs_pos]; exact sub_ne_zero.mpr hz₀
  have hδ2pos : 0 < δ / 2 := half_pos hδpos
  let s : Set ℂ := Metric.ball z₀ (δ / 2)
  have hs_nhds : s ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ hδ2pos
  have hs_ev : ∀ᶠ x in 𝓝 z₀, x ∈ s := hs_nhds
  -- the distance from `z` to the singular line is bounded below on `s`
  have hden : ∀ z ∈ s, ∀ t : ℝ, δ / 2 ≤ ‖(a : ℂ) + (t : ℂ) * Complex.I - z‖ := by
    intro z hz t
    have hz' : dist z z₀ < δ / 2 := Metric.mem_ball.mp hz
    have htri : |z₀.re - a| ≤ |z₀.re - z.re| + |z.re - a| := by
      have h : z₀.re - a = (z₀.re - z.re) + (z.re - a) := by ring
      calc |z₀.re - a| = |(z₀.re - z.re) + (z.re - a)| := by rw [h]
        _ ≤ |z₀.re - z.re| + |z.re - a| := abs_add_le _ _
    have hre1 : |z₀.re - z.re| ≤ ‖z₀ - z‖ := by
      have := Complex.abs_re_le_norm (z₀ - z)
      simpa [Complex.sub_re] using this
    have hdist : ‖z₀ - z‖ < δ / 2 := by rw [← dist_eq_norm, dist_comm]; exact hz'
    have h3 : |z₀.re - z.re| < δ / 2 := lt_of_le_of_lt hre1 hdist
    have h4 : δ / 2 < |z.re - a| := by
      have hlt : δ < δ / 2 + |z.re - a| :=
        calc δ = |z₀.re - a| := hδeq
          _ ≤ |z₀.re - z.re| + |z.re - a| := htri
          _ < δ / 2 + |z.re - a| := by linarith [h3]
      linarith
    have hre : ((a : ℂ) + (t : ℂ) * Complex.I - z).re = a - z.re := by simp
    calc δ / 2 ≤ |z.re - a| := le_of_lt h4
      _ = |((a : ℂ) + (t : ℂ) * Complex.I - z).re| := by rw [hre, abs_sub_comm]
      _ ≤ ‖(a : ℂ) + (t : ℂ) * Complex.I - z‖ := Complex.abs_re_le_norm _
  have hne : ∀ z ∈ s, ∀ t : ℝ, (a : ℂ) + (t : ℂ) * Complex.I - z ≠ 0 :=
    fun z hz t => norm_pos_iff.mp (lt_of_lt_of_le hδ2pos (hden z hz t))
  let G : ℂ → ℝ → ℂ := fun z t => ((a : ℂ) + (t : ℂ) * Complex.I - z)⁻¹ * F t
  let G' : ℂ → ℝ → ℂ := fun z t => (1 / ((a : ℂ) + (t : ℂ) * Complex.I - z)^2) * F t
  let bound : ℝ → ℝ := fun _ => ((δ/2)^2)⁻¹ * |M|
  -- the integrand is a.e.-strongly-measurable near `z₀`
  have hG_meas : ∀ᶠ x in 𝓝 z₀, AEStronglyMeasurable (G x) (volume.restrict (uIoc c d)) := by
    refine hs_ev.mono (fun x hx => ?_)
    have hcont : Continuous fun t : ℝ => ((a : ℂ) + (t : ℂ) * Complex.I - x)⁻¹ := by
      refine Continuous.inv₀ ?_ (fun t => hne x hx t)
      fun_prop
    have h2 := hcont.aestronglyMeasurable.mul hfm
    have hfun : ((fun t : ℝ => ((a : ℂ) + (t : ℂ) * Complex.I - x)⁻¹) * F)
        = (fun t : ℝ => ((a : ℂ) + (t : ℂ) * Complex.I - x)⁻¹ * F t) := rfl
    rw [hfun] at h2
    simpa only [G] using h2
  -- the integrand is integrable at `z₀`
  have hF_int : IntervalIntegrable (G z₀) volume c d := by
    refine IntervalIntegrable.mono_fun' (intervalIntegrable_const (c := (δ/2)⁻¹ * |M|)) ?_ ?_
    · exact hG_meas.self_of_nhds
    · filter_upwards [hfb] with t ht
      have hb := hden z₀ (Metric.mem_ball_self hδ2pos) t
      have hu : ‖((a : ℂ) + (t : ℂ) * Complex.I - z₀)⁻¹‖ ≤ (δ/2)⁻¹ := by
        rw [norm_inv]
        exact (inv_le_inv₀ (lt_of_lt_of_le hδ2pos hb) hδ2pos).mpr hb
      calc ‖G z₀ t‖ = ‖((a : ℂ) + (t : ℂ) * Complex.I - z₀)⁻¹ * F t‖ := by simp only [G]
        _ ≤ ‖((a : ℂ) + (t : ℂ) * Complex.I - z₀)⁻¹‖ * ‖F t‖ := norm_mul_le _ _
        _ ≤ (δ/2)⁻¹ * |M| :=
            mul_le_mul hu (le_trans ht (le_abs_self M)) (norm_nonneg _)
              (le_of_lt (inv_pos.mpr hδ2pos))
  -- the derivative is a.e.-strongly-measurable at `z₀`
  have hG'_meas : AEStronglyMeasurable (G' z₀) (volume.restrict (uIoc c d)) := by
    have hcont : Continuous fun t : ℝ => 1 / ((a : ℂ) + (t : ℂ) * Complex.I - z₀)^2 := by
      refine Continuous.div continuous_const ?_
        (fun t => pow_ne_zero 2 (hne z₀ (Metric.mem_ball_self hδ2pos) t))
      fun_prop
    have h2 := hcont.aestronglyMeasurable.mul hfm
    have hfun : ((fun t : ℝ => 1 / ((a : ℂ) + (t : ℂ) * Complex.I - z₀)^2) * F)
        = (fun t : ℝ => 1 / ((a : ℂ) + (t : ℂ) * Complex.I - z₀)^2 * F t) := rfl
    rw [hfun] at h2
    simpa only [G'] using h2
  -- the derivative is dominated by an integrable constant
  have hG'bound : ∀ᵐ t ∂volume, t ∈ uIoc c d → ∀ z ∈ s, ‖G' z t‖ ≤ bound t := by
    have hFaeb : ∀ᵐ t ∂volume, t ∈ uIoc c d → ‖F t‖ ≤ M :=
      (ae_restrict_iff' measurableSet_uIoc).mp hfb
    filter_upwards [hFaeb] with t ht
    intro _ht z hz
    have hb := hden z hz t
    have hnorm : ‖(1 / ((a : ℂ) + (t : ℂ) * Complex.I - z)^2)‖ ≤ ((δ/2)^2)⁻¹ := by
      rw [one_div, norm_inv, norm_pow]
      exact (inv_le_inv₀ (pow_pos (lt_of_lt_of_le hδ2pos hb) 2) (pow_pos hδ2pos 2)).mpr
        (pow_le_pow_left₀ (le_of_lt hδ2pos) hb 2)
    calc ‖G' z t‖ = ‖(1 / ((a : ℂ) + (t : ℂ) * Complex.I - z)^2) * F t‖ := by simp only [G']
      _ ≤ ‖(1 / ((a : ℂ) + (t : ℂ) * Complex.I - z)^2)‖ * ‖F t‖ := norm_mul_le _ _
      _ ≤ ((δ/2)^2)⁻¹ * |M| :=
          mul_le_mul hnorm (le_trans (ht _ht) (le_abs_self M)) (norm_nonneg _)
            (inv_nonneg.mpr (pow_nonneg (le_of_lt hδ2pos) 2))
      _ = bound t := by simp only [bound]
  have hbound_int : IntervalIntegrable bound volume c d := by
    simpa only [bound] using
      (intervalIntegrable_const (c := ((δ/2)^2)⁻¹ * |M|) :
        IntervalIntegrable (fun _ : ℝ => ((δ/2)^2)⁻¹ * |M|) volume c d)
  -- pointwise `z`-derivative of the integrand
  have h_diff : ∀ᵐ t ∂volume, t ∈ uIoc c d → ∀ z ∈ s, HasDerivAt (fun y => G y t) (G' z t) z := by
    filter_upwards with t
    intro _ht z hz
    have h1 : HasDerivAt (fun y : ℂ => (a : ℂ) + (t : ℂ) * Complex.I - y) (-1) z := by
      simpa using (hasDerivAt_id z).const_sub ((a : ℂ) + (t : ℂ) * Complex.I)
    have h2 := (h1.inv (hne z hz t)).mul_const (F t)
    simpa [G, G'] using h2
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := G) (F' := G') (x₀ := z₀) (s := s) (μ := volume) (bound := bound)
    (a := c) (b := d) hs_nhds hG_meas hF_int hG'_meas hG'bound hbound_int h_diff
  simpa only [G] using (hmain.2.differentiableAt).differentiableWithinAt

end Work.TMComp.RedC8
