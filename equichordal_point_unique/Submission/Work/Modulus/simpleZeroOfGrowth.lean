import Mathlib

namespace Work.Modulus

open Filter Set
open scoped Topology

theorem simpleZeroOfGrowth {g : ℂ → ℂ} {a : ℂ} {ε C₁ C₂ : ℝ} (hε : 0 < ε) (hC₂ : 0 < C₂)
    (hg : AnalyticAt ℂ g a)
    (hup : ∀ w ∈ Metric.ball a ε, w ≠ a → ‖g w‖ ≤ C₁ * ‖w - a‖)
    (hlo : ∀ w ∈ Metric.ball a ε, w ≠ a → C₂ * ‖w - a‖ ≤ ‖g w‖) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F a ∧ F a ≠ 0 ∧ g =ᶠ[nhds a] fun w => (w - a) * F w := by
  have hball : ∀ᶠ w in 𝓝[≠] a, w ∈ Metric.ball a ε :=
    Eventually.filter_mono nhdsWithin_le_nhds (Metric.ball_mem_nhds a hε)
  have hne : ∀ᶠ w in 𝓝[≠] a, w ≠ a := by
    filter_upwards [self_mem_nhdsWithin] with w hw using hw
  have hupper_tend : Tendsto (fun w : ℂ => C₁ * ‖w - a‖) (𝓝[≠] a) (𝓝 0) := by
    have h1 : Tendsto (fun w : ℂ => w - a) (𝓝 a) (𝓝 0) := by
      simpa only [Pi.sub_apply, id_eq, sub_self] using
        (tendsto_id.sub (tendsto_const_nhds (x := a)) :
          Tendsto (fun w : ℂ => id w - a) (𝓝 a) (𝓝 (a - a)))
    have h2 : Tendsto (fun w : ℂ => ‖w - a‖) (𝓝 a) (𝓝 0) := by simpa using h1.norm
    exact (show Tendsto (fun w : ℂ => C₁ * ‖w - a‖) (𝓝 a) (𝓝 0) by
      simpa using h2.const_mul C₁).mono_left nhdsWithin_le_nhds
  -- the function vanishes at `a`
  have hga : g a = 0 := by
    have hzero : Tendsto g (𝓝[≠] a) (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hupper_tend
      filter_upwards [hball, hne] with w hw hwne
      exact hup w hw hwne
    have hcont : Tendsto g (𝓝[≠] a) (𝓝 (g a)) :=
      hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact (tendsto_nhds_unique hzero hcont).symm
  -- the derivative at `a` does not vanish
  have hderiv : deriv g a ≠ 0 := by
    have hslope : Tendsto (slope g a) (𝓝[≠] a) (𝓝 (deriv g a)) :=
      hg.differentiableAt.hasDerivAt.tendsto_slope
    have hnorm : Tendsto (fun w => ‖slope g a w‖) (𝓝[≠] a) (𝓝 ‖deriv g a‖) := by
      simpa using hslope.norm
    have hge : ∀ᶠ w in 𝓝[≠] a, C₂ ≤ ‖slope g a w‖ := by
      filter_upwards [hball, hne] with w hw hwne
      have hxa : 0 < ‖w - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hwne)
      have hxx : ‖w - a‖⁻¹ * ‖w - a‖ = 1 := inv_mul_cancel₀ hxa.ne'
      have h1 : ‖w - a‖⁻¹ * (C₂ * ‖w - a‖) = C₂ := by
        calc ‖w - a‖⁻¹ * (C₂ * ‖w - a‖) = C₂ * (‖w - a‖⁻¹ * ‖w - a‖) := by ring
          _ = C₂ * 1 := by rw [hxx]
          _ = C₂ := mul_one C₂
      have h2 : C₂ ≤ ‖w - a‖⁻¹ * ‖g w‖ :=
        h1.ge.trans (mul_le_mul_of_nonneg_left (hlo w hw hwne) (inv_nonneg.mpr hxa.le))
      rwa [slope_def_module, hga, sub_zero, smul_eq_mul, norm_mul, norm_inv]
    have hle : C₂ ≤ ‖deriv g a‖ := ge_of_tendsto hnorm hge
    intro hzero
    rw [hzero, norm_zero] at hle
    linarith
  have horder : analyticOrderAt g a = 1 :=
    hg.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hga hderiv
  obtain ⟨F, hF, hF0, hFg⟩ := (hg.analyticOrderAt_eq_natCast (n := 1)).mp horder
  refine ⟨F, hF, hF0, ?_⟩
  filter_upwards [hFg] with z hz
  simpa [pow_one, smul_eq_mul] using hz

end Work.Modulus
