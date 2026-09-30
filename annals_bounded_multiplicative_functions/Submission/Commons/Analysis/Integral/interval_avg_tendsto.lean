import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Set Filter Metric
open scoped Topology Interval

namespace Commons.Analysis.Integral

lemma interval_avg_tendsto (f : ℝ → ℂ) {t₀ : ℝ} (hf : Continuous f) :
    Filter.Tendsto (fun τ : ℝ => (1 / (2 * τ)) • intervalIntegral f (t₀ - τ) (t₀ + τ) (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f t₀)) := by
  change Filter.Tendsto
    (fun τ : ℝ => (1 / (2 * τ)) • (∫ x in (t₀ - τ)..(t₀ + τ), f x ∂volume))
    (𝓝[>] 0) (𝓝 (f t₀))
  let g : ℝ → ℂ := fun x => f x - f t₀
  have hg : Continuous g := by
    change Continuous (fun x : ℝ => f x - f t₀)
    exact hf.sub (continuous_const : Continuous (fun _ : ℝ => f t₀))
  have hg0 : g t₀ = 0 := by simp [g]
  -- The function of the perturbation part tends to zero at 0⁺.
  have hB : Tendsto
      (fun τ : ℝ => (1 / (2 * τ)) • (∫ x in (t₀ - τ)..(t₀ + τ), g x ∂volume))
      (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hε2 : 0 < ε / 2 := half_pos hε
    have hnorm_tendsto : Tendsto (fun x : ℝ => ‖g x‖) (𝓝 t₀) (𝓝 (0 : ℝ)) := by
      simpa [hg0] using
        (ContinuousAt.tendsto (ContinuousAt.norm (hg.continuousAt (x := t₀))))
    have h_ev : ∀ᶠ x in 𝓝 t₀, ‖g x‖ < ε / 2 := by
      have h' := Metric.tendsto_nhds.mp hnorm_tendsto (ε / 2) hε2
      filter_upwards [h'] with x hx
      simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg (g x))] using hx
    rcases Metric.eventually_nhds_iff.mp h_ev with ⟨δ, hδ0, hδball⟩
    have hb : ∀ x : ℝ, |x - t₀| < δ → ‖g x‖ < ε / 2 := by
      intro x hx
      exact hδball (by simpa [Real.dist_eq] using hx)
    filter_upwards [Ioo_mem_nhdsGT hδ0] with τ hτIoo
    have hτ0 : 0 < τ := (Set.mem_Ioo.mp hτIoo).1
    have hτδ : τ < δ := (Set.mem_Ioo.mp hτIoo).2
    have hab : t₀ - τ ≤ t₀ + τ := by linarith
    have hxboundIcc : ∀ x ∈ Set.Icc (t₀ - τ) (t₀ + τ), ‖g x‖ ≤ ε / 2 := by
      intro x hxIcc
      have hxabs : |x - t₀| ≤ τ := by
        rw [abs_sub_le_iff]
        constructor
        · linarith [hxIcc.2]
        · linarith [hxIcc.1]
      have hxδ : |x - t₀| < δ := lt_of_le_of_lt hxabs hτδ
      exact le_of_lt (hb x hxδ)
    have hnormI : ‖∫ x in (t₀ - τ)..(t₀ + τ), g x ∂volume‖ ≤ (ε / 2) * (2 * τ) := by
      have hnorm_bnd :
          ‖∫ x in (t₀ - τ)..(t₀ + τ), g x ∂volume‖ ≤
            ∫ x in (t₀ - τ)..(t₀ + τ), ‖g x‖ ∂volume := by
        exact intervalIntegral.norm_integral_le_integral_norm (f := g) (μ := volume) hab
      have hmono :
          (∫ x in (t₀ - τ)..(t₀ + τ), ‖g x‖ ∂volume) ≤
            (∫ x in (t₀ - τ)..(t₀ + τ), (ε / 2 : ℝ) ∂volume) := by
        exact intervalIntegral.integral_mono_on (a := t₀ - τ) (b := t₀ + τ) (μ := volume) hab
          (hg.norm.intervalIntegrable (t₀ - τ) (t₀ + τ)) (intervalIntegrable_const) hxboundIcc
      have hconst : (∫ x in (t₀ - τ)..(t₀ + τ), (ε / 2 : ℝ) ∂volume) = (ε / 2) * (2 * τ) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        ring
      calc
        ‖∫ x in (t₀ - τ)..(t₀ + τ), g x ∂volume‖
            ≤ ∫ x in (t₀ - τ)..(t₀ + τ), ‖g x‖ ∂volume := hnorm_bnd
        _ ≤ (∫ x in (t₀ - τ)..(t₀ + τ), (ε / 2 : ℝ) ∂volume) := hmono
        _ = (ε / 2) * (2 * τ) := hconst
    have h2pos : 0 < 2 * τ := mul_pos zero_lt_two hτ0
    have hnormB : ‖(1 / (2 * τ)) • (∫ x in (t₀ - τ)..(t₀ + τ), g x ∂volume)‖ ≤ ε / 2 := by
      calc
        ‖(1 / (2 * τ)) • (∫ x in (t₀ - τ)..(t₀ + τ), g x ∂volume)‖
            = (1 / (2 * τ)) * ‖∫ x in (t₀ - τ)..(t₀ + τ), g x ∂volume‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg]
              exact le_of_lt (one_div_pos.mpr h2pos)
        _ ≤ (1 / (2 * τ)) * ((ε / 2) * (2 * τ)) := by
              exact mul_le_mul_of_nonneg_left hnormI (le_of_lt (one_div_pos.mpr h2pos))
        _ = ε / 2 := by
              calc
                (1 / (2 * τ)) * ((ε / 2) * (2 * τ)) = (1 / (2 * τ)) * (2 * τ) * (ε / 2) := by ring
                _ = 1 * (ε / 2) := by rw [one_div_mul_cancel (ne_of_gt h2pos)]
                _ = ε / 2 := by simp
    simpa [dist_eq_norm] using lt_of_le_of_lt hnormB (half_lt_self hε)
  -- The main term equals f t₀ plus the perturbation, eventually for τ > 0.
  have hmain : (fun τ : ℝ => (1 / (2 * τ)) • (∫ x in (t₀ - τ)..(t₀ + τ), f x ∂volume)) =ᶠ[𝓝[>] 0]
      (fun τ : ℝ => f t₀ + (1 / (2 * τ)) • (∫ x in (t₀ - τ)..(t₀ + τ), g x ∂volume)) := by
    filter_upwards [self_mem_nhdsWithin] with τ hτmem
    have hτ0 : 0 < τ := by simpa using hτmem
    have hfg : (fun x : ℝ => f x) = fun x : ℝ => f t₀ + g x := by
      funext x
      simp [g]
    have hgI : IntervalIntegrable g volume (t₀ - τ) (t₀ + τ) := hg.intervalIntegrable _ _
    have hconstI : IntervalIntegrable (fun _ : ℝ => (f t₀ : ℂ)) volume (t₀ - τ) (t₀ + τ) :=
      intervalIntegrable_const
    have hdecomp : (∫ x in (t₀ - τ)..(t₀ + τ), f x ∂volume) =
        (∫ x in (t₀ - τ)..(t₀ + τ), (f t₀ : ℂ) ∂volume) +
          ∫ x in (t₀ - τ)..(t₀ + τ), g x ∂volume := by
      calc
        (∫ x in (t₀ - τ)..(t₀ + τ), f x ∂volume) =
            ∫ x in (t₀ - τ)..(t₀ + τ), f t₀ + g x ∂volume := by rw [← hfg]
        _ = (∫ x in (t₀ - τ)..(t₀ + τ), (f t₀ : ℂ) ∂volume) +
              ∫ x in (t₀ - τ)..(t₀ + τ), g x ∂volume := by
              exact intervalIntegral.integral_add (f := fun _ : ℝ => (f t₀ : ℂ)) (g := g)
                hconstI hgI
    have hcint : (∫ x in (t₀ - τ)..(t₀ + τ), (f t₀ : ℂ) ∂volume) = (2 * τ) • (f t₀ : ℂ) := by
      rw [intervalIntegral.integral_const]
      congr 1
      ring
    have h2ne : (2 * τ) ≠ 0 := ne_of_gt (mul_pos zero_lt_two hτ0)
    calc
      (1 / (2 * τ)) • (∫ x in (t₀ - τ)..(t₀ + τ), f x ∂volume)
          = (1 / (2 * τ)) • ((∫ x in (t₀ - τ)..(t₀ + τ), (f t₀ : ℂ) ∂volume) +
              ∫ x in (t₀ - τ)..(t₀ + τ), g x ∂volume) := by rw [hdecomp]
      _ = (1 / (2 * τ)) • ((2 * τ) • (f t₀ : ℂ) + ∫ x in (t₀ - τ)..(t₀ + τ), g x ∂volume) := by
              rw [hcint]
      _ = (f t₀ : ℂ) + (1 / (2 * τ)) • (∫ x in (t₀ - τ)..(t₀ + τ), g x ∂volume) := by
              rw [smul_add, smul_smul, one_div_mul_cancel h2ne, one_smul]
  have hCB : Tendsto
      (fun τ : ℝ => (f t₀ : ℂ) + (1 / (2 * τ)) • (∫ x in (t₀ - τ)..(t₀ + τ), g x ∂volume))
      (𝓝[>] 0) (𝓝 (f t₀ : ℂ)) := by
    have hc : Tendsto (fun _ : ℝ => (f t₀ : ℂ)) (𝓝[>] 0) (𝓝 (f t₀ : ℂ)) := tendsto_const_nhds
    simpa using hc.add hB
  exact hCB.congr' hmain.symm

end Commons.Analysis.Integral