import Mathlib

set_option maxHeartbeats 1000000

namespace Work.OddVolterra.Abel

open MeasureTheory Filter
open scoped Interval Topology

/-- Differentiation under the integral sign for the (non-singular) fixed-interval Abel
transform `u ↦ ∫_c^1 (√(v - u))⁻¹ • Q v dv` at a point `x` strictly to the left of the
interval `[c,1]`.

Here the kernel `v ↦ (√(v - u))⁻¹` is smooth on a neighbourhood of the integration
interval (the singularity `v = u` lies outside `[c,1]`), so `Q` only needs to be
continuous. -/
theorem abel_fixed_interval_diff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {c x : ℝ} (hxc : x < c) (hc1 : c ≤ 1) {Q : ℝ → E}
    (hQcont : ContinuousOn Q (Set.Icc c 1)) :
    DifferentiableAt ℝ (fun u : ℝ => ∫ v in c..1, (Real.sqrt (v - u))⁻¹ • Q v) x := by
  classical
  -- The singularity `v = u` stays a positive distance away from `[c,1]` for `u` near `x`.
  set δ : ℝ := (c - x) / 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact half_pos (sub_pos.mpr hxc)
  set s : Set ℝ := Metric.ball x δ with hsdef
  have hs_nhds : s ∈ 𝓝 x := Metric.ball_mem_nhds x hδpos
  have hs_lt : ∀ u ∈ s, u < c - δ := by
    intro u hu
    have h : |u - x| < δ := by
      rw [hsdef, Metric.mem_ball, Real.dist_eq] at hu
      exact hu
    linarith [(abs_lt.mp h).2]
  have hx_mem : x ∈ s := by rw [hsdef]; exact Metric.mem_ball_self hδpos
  set F : ℝ → ℝ → E := fun u v => (Real.sqrt (v - u))⁻¹ • Q v with hFdef
  set F' : ℝ → ℝ → E := fun u v => ((2 * (Real.sqrt (v - u)) ^ 3)⁻¹) • Q v with hF'def
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hQcont
  set bound : ℝ → ℝ := fun _ => (2 * (Real.sqrt δ) ^ 3)⁻¹ * M with hbounddef
  have hbound_int : IntervalIntegrable bound volume c 1 := by
    rw [hbounddef]; exact intervalIntegrable_const
  have hQ' : ContinuousOn Q (Set.uIcc c 1) := by rw [Set.uIcc_of_le hc1]; exact hQcont
  -- Continuity of the kernel on `[c,1]` as long as `u < c - δ`.
  have hker_cont : ∀ u : ℝ, u < c - δ →
      ContinuousOn (fun v : ℝ => (Real.sqrt (v - u))⁻¹ • Q v) (Set.uIcc c 1) := by
    intro u hu
    have hne : ∀ v ∈ Set.uIcc c 1, Real.sqrt (v - u) ≠ 0 := by
      intro v hv
      have hv' : v ∈ Set.Icc c 1 := by rw [Set.uIcc_of_le hc1] at hv; exact hv
      exact ne_of_gt (Real.sqrt_pos.mpr (by linarith [hv'.1]))
    have hden : ContinuousOn (fun v : ℝ => Real.sqrt (v - u)) (Set.uIcc c 1) :=
      (Real.continuous_sqrt.comp
        (continuous_id.sub continuous_const : Continuous (fun v : ℝ => v - u))).continuousOn
    exact (hden.inv₀ hne).smul hQ'
  have hF_meas : ∀ᶠ u in 𝓝 x, AEStronglyMeasurable (F u) (volume.restrict (Set.uIoc c 1)) := by
    filter_upwards [hs_nhds] with u hu
    have h := (hker_cont u (hs_lt u hu)).aestronglyMeasurable_of_subset_isCompact
      isCompact_uIcc measurableSet_uIoc Set.uIoc_subset_uIcc (μ := volume)
    rw [hFdef]
    exact h
  have hF_int : IntervalIntegrable (F x) volume c 1 := by
    have hcont := hker_cont x (hs_lt x hx_mem)
    have h2 : IntervalIntegrable (fun v : ℝ => (Real.sqrt (v - x))⁻¹ • Q v) volume c 1 :=
      hcont.intervalIntegrable
    rw [hFdef]
    exact h2
  -- Continuity of the candidate derivative kernel on `[c,1]`.
  have hker'_cont : ∀ u : ℝ, u < c - δ →
      ContinuousOn (fun v : ℝ => ((2 : ℝ) * (Real.sqrt (v - u)) ^ 3)⁻¹ • Q v)
        (Set.uIcc c 1) := by
    intro u hu
    have hne : ∀ v ∈ Set.uIcc c 1, (2 : ℝ) * (Real.sqrt (v - u)) ^ 3 ≠ 0 := by
      intro v hv
      have hv' : v ∈ Set.Icc c 1 := by rw [Set.uIcc_of_le hc1] at hv; exact hv
      have hpos : 0 < Real.sqrt (v - u) := Real.sqrt_pos.mpr (by linarith [hv'.1])
      exact ne_of_gt (mul_pos (by norm_num) (pow_pos hpos 3))
    have hden : ContinuousOn (fun v : ℝ => (2 : ℝ) * (Real.sqrt (v - u)) ^ 3)
        (Set.uIcc c 1) :=
      continuousOn_const.mul (((Real.continuous_sqrt.comp
        (continuous_id.sub continuous_const : Continuous (fun v : ℝ => v - u))).continuousOn).pow 3)
    exact (hden.inv₀ hne).smul hQ'
  have hF'_meas : AEStronglyMeasurable (F' x) (volume.restrict (Set.uIoc c 1)) := by
    have h := (hker'_cont x (hs_lt x hx_mem)).aestronglyMeasurable_of_subset_isCompact
      isCompact_uIcc measurableSet_uIoc Set.uIoc_subset_uIcc (μ := volume)
    rw [hF'def]
    exact h
  -- Uniform bound on the derivative kernel over `s`.
  have h_bound : ∀ᵐ t ∂volume, t ∈ Set.uIoc c 1 → ∀ u ∈ s, ‖F' u t‖ ≤ bound t := by
    refine Filter.Eventually.of_forall fun t ht u hu => ?_
    have ht' : t ∈ Set.Ioc c 1 := by rw [Set.uIoc_of_le hc1] at ht; exact ht
    have hu_lt : u < c - δ := hs_lt u hu
    have htu : δ < t - u := by linarith [ht'.1]
    have hδnn : 0 ≤ δ := le_of_lt hδpos
    have hspos : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδpos
    have hspos2 : 0 < Real.sqrt (t - u) := Real.sqrt_pos.mpr (by linarith)
    have hsqrt_lt : Real.sqrt δ < Real.sqrt (t - u) := Real.sqrt_lt_sqrt hδnn htu
    have hcube : 2 * (Real.sqrt δ) ^ 3 < 2 * (Real.sqrt (t - u)) ^ 3 := by
      have h3 : (Real.sqrt δ) ^ 3 < (Real.sqrt (t - u)) ^ 3 :=
        pow_lt_pow_left₀ hsqrt_lt (le_of_lt hspos) (by norm_num)
      linarith
    have hApos : 0 < 2 * (Real.sqrt (t - u)) ^ 3 := mul_pos (by norm_num) (pow_pos hspos2 3)
    have hBpos : 0 < 2 * (Real.sqrt δ) ^ 3 := mul_pos (by norm_num) (pow_pos hspos 3)
    have hcoef : |((2 * (Real.sqrt (t - u)) ^ 3)⁻¹ : ℝ)| ≤ (2 * (Real.sqrt δ) ^ 3)⁻¹ := by
      rw [abs_of_nonneg (le_of_lt (inv_pos.mpr hApos))]
      exact le_of_lt ((inv_lt_inv₀ hApos hBpos).mpr hcube)
    have hQt : ‖Q t‖ ≤ M := hM t ⟨le_of_lt ht'.1, ht'.2⟩
    calc ‖F' u t‖ = |((2 * (Real.sqrt (t - u)) ^ 3)⁻¹ : ℝ)| * ‖Q t‖ := by
            simp only [hF'def, norm_smul, Real.norm_eq_abs]
      _ ≤ (2 * (Real.sqrt δ) ^ 3)⁻¹ * M :=
            mul_le_mul hcoef hQt (norm_nonneg _) (le_of_lt (inv_pos.mpr hBpos))
      _ = bound t := by rw [hbounddef]
  -- Pointwise differentiability of the integrand in the first variable.
  have h_diff : ∀ᵐ t ∂volume, t ∈ Set.uIoc c 1 → ∀ u ∈ s,
      HasDerivAt (fun y : ℝ => F y t) (F' u t) u := by
    refine Filter.Eventually.of_forall fun t ht u hu => ?_
    have ht' : t ∈ Set.Ioc c 1 := by rw [Set.uIoc_of_le hc1] at ht; exact ht
    have hu_lt : u < c - δ := hs_lt u hu
    have htu : 0 < t - u := by linarith [ht'.1]
    have hsne : Real.sqrt (t - u) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr htu)
    have hlin : HasDerivAt (fun y : ℝ => t - y) (-1) u := (hasDerivAt_id u).const_sub t
    have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (t - u))) (t - u) :=
      Real.hasDerivAt_sqrt (ne_of_gt htu)
    have hkey : (-((Real.sqrt (t - u)) ^ 2)⁻¹) * ((1 / (2 * Real.sqrt (t - u))) * (-1))
        = (2 * (Real.sqrt (t - u)) ^ 3)⁻¹ := by
      field_simp
    have hk := ((hasDerivAt_inv hsne).comp u (hsqrt.comp u hlin)).congr_deriv hkey
    have hsm := hk.smul_const (Q t)
    simpa [hFdef, hF'def, Function.comp] using hsm
  have hdom := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (μ := volume) (E := E) (a := c) (b := 1)
    (F := F) (F' := F') (x₀ := x) (s := s) (bound := bound)
    hs_nhds hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  simpa [hFdef] using hdom.2.differentiableAt

end Work.OddVolterra.Abel
