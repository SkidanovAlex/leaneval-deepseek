import Mathlib

namespace Work.Asymptotics.KaxisMid

open Metric Set Filter Complex
open scoped Topology

/-- **Two-zero bound.**  A function holomorphic on the disc `ball c ρ` which vanishes at two
*distinct* points `z₁ z₂` of the disc of half the radius is bounded there by
`(4 M / ρ²) ‖z - z₁‖ ‖z - z₂‖`, where `M` bounds `‖f‖` on `ball c ρ`. -/
theorem norm_le_of_norm_le_of_two_zeros {f : ℂ → ℂ} {c : ℂ} {ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 ≤ M)
    (hf : DiffContOnCl ℂ f (Metric.ball c ρ)) (hbd : ∀ z ∈ Metric.ball c ρ, ‖f z‖ ≤ M)
    {z₁ z₂ : ℂ} (h₁ : z₁ ∈ Metric.ball c (ρ / 2)) (h₂ : z₂ ∈ Metric.ball c (ρ / 2))
    (hne : z₁ ≠ z₂) (hf₁ : f z₁ = 0) (hf₂ : f z₂ = 0) :
    ∀ z ∈ Metric.ball c (ρ / 2), ‖f z‖ ≤ (4 * M / ρ ^ 2) * ‖z - z₁‖ * ‖z - z₂‖ := by
  intro z hz
  -- The quotient `g w = f w / ((w - z₁) (w - z₂))` is the double divided difference of `f`
  -- at `z₁` and `z₂`; it is holomorphic on the whole disc `ball c ρ`.
  have hz₁ρ : z₁ ∈ Metric.ball c ρ := Metric.ball_subset_ball (by linarith) h₁
  have hz₂ρ : z₂ ∈ Metric.ball c ρ := Metric.ball_subset_ball (by linarith) h₂
  have hd₁ : DifferentiableOn ℂ (dslope f z₁) (Metric.ball c ρ) :=
    (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds hz₁ρ)).mpr hf.differentiableOn
  have hd₂ : DifferentiableOn ℂ (dslope (dslope f z₁) z₂) (Metric.ball c ρ) :=
    (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds hz₂ρ)).mpr hd₁
  have hz₂zero : dslope f z₁ z₂ = 0 := by
    rw [dslope_of_ne _ hne.symm, slope_def_module, hf₂, hf₁, sub_self, smul_zero]
  -- The factorisation `f w = (w - z₁) (w - z₂) g w`.
  have hfac₁ : ∀ w : ℂ, (w - z₁) * dslope f z₁ w = f w := by
    intro w; simpa using sub_smul_dslope_of_zero hf₁ w
  have hfac₂ : ∀ w : ℂ, (w - z₂) * dslope (dslope f z₁) z₂ w = dslope f z₁ w := by
    intro w; simpa using sub_smul_dslope_of_zero hz₂zero w
  have hfac : ∀ w : ℂ, f w = (w - z₁) * (w - z₂) * dslope (dslope f z₁) z₂ w := by
    intro w; rw [← hfac₁ w, ← hfac₂ w]; ring
  -- Maximum modulus estimate for the quotient on the disc of radius `r < ρ`.
  have hbound : ‖dslope (dslope f z₁) z₂ z‖ ≤ 4 * M / ρ ^ 2 := by
    have key : ∀ᶠ r in 𝓝[<] ρ, ‖dslope (dslope f z₁) z₂ z‖ ≤ M / (r - ρ / 2) ^ 2 := by
      filter_upwards [Ioo_mem_nhdsLT (show ρ / 2 < ρ by linarith)] with r hr
      obtain ⟨hrl, hrr⟩ := hr
      have hzr : z ∈ Metric.ball c r := Metric.mem_ball.mpr (by
        have := Metric.mem_ball.mp hz; linarith)
      have hgd : DiffContOnCl ℂ (dslope (dslope f z₁) z₂) (Metric.ball c r) :=
        hd₂.diffContOnCl_ball (Metric.closedBall_subset_ball hrr)
      have hpos : 0 < (r - ρ / 2) ^ 2 := by nlinarith
      refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hgd ?_
        (subset_closure hzr)
      intro w hw
      have hws : w ∈ Metric.sphere c r := frontier_ball_subset_sphere hw
      have hwr : dist w c = r := Metric.mem_sphere.mp hws
      have hwρ : w ∈ Metric.ball c ρ := Metric.mem_ball.mpr (by rw [hwr]; exact hrr)
      have hfw := hbd w hwρ
      have hfwn : ‖f w‖ = ‖w - z₁‖ * ‖w - z₂‖ * ‖dslope (dslope f z₁) z₂ w‖ := by
        rw [hfac w, norm_mul, norm_mul]
      have hd₁w : r - ρ / 2 ≤ ‖w - z₁‖ := by
        have ht : r ≤ ‖w - z₁‖ + dist z₁ c := by
          have := dist_triangle w z₁ c
          rw [hwr] at this
          simpa [dist_eq_norm] using this
        have hz₁c : dist z₁ c < ρ / 2 := Metric.mem_ball.mp h₁
        linarith
      have hd₂w : r - ρ / 2 ≤ ‖w - z₂‖ := by
        have ht : r ≤ ‖w - z₂‖ + dist z₂ c := by
          have := dist_triangle w z₂ c
          rw [hwr] at this
          simpa [dist_eq_norm] using this
        have hz₂c : dist z₂ c < ρ / 2 := Metric.mem_ball.mp h₂
        linarith
      rw [le_div_iff₀ hpos]
      have hnn : 0 ≤ r - ρ / 2 := by linarith
      have hmul : (r - ρ / 2) ^ 2 ≤ ‖w - z₁‖ * ‖w - z₂‖ := by
        rw [pow_two]
        exact mul_le_mul (a := r - ρ / 2) (b := ‖w - z₁‖) (c := r - ρ / 2)
          (d := ‖w - z₂‖) hd₁w hd₂w hnn (norm_nonneg _)
      calc ‖dslope (dslope f z₁) z₂ w‖ * (r - ρ / 2) ^ 2
          = (r - ρ / 2) ^ 2 * ‖dslope (dslope f z₁) z₂ w‖ := by ring
        _ ≤ (‖w - z₁‖ * ‖w - z₂‖) * ‖dslope (dslope f z₁) z₂ w‖ :=
              mul_le_mul_of_nonneg_right hmul (norm_nonneg _)
        _ = ‖f w‖ := by rw [hfwn]
        _ ≤ M := hfw
    -- Let `r → ρ` to obtain the sharp constant.
    have hne2 : (ρ - ρ / 2) ^ 2 ≠ 0 := by
      have : ρ - ρ / 2 ≠ 0 := by linarith
      positivity
    have hc : ContinuousAt (fun r : ℝ => M / (r - ρ / 2) ^ 2) ρ :=
      ContinuousAt.div continuousAt_const ((continuousAt_id.sub continuousAt_const).pow 2) hne2
    have hval : M / (ρ - ρ / 2) ^ 2 = M / (ρ / 2) ^ 2 := by
      rw [show ρ - ρ / 2 = ρ / 2 by ring]
    have htend : Tendsto (fun r : ℝ => M / (r - ρ / 2) ^ 2) (𝓝[<] ρ) (𝓝 (M / (ρ / 2) ^ 2)) := by
      rw [← hval]
      exact hc.tendsto.mono_left nhdsWithin_le_nhds
    have hlim := ge_of_tendsto htend key
    have heq : M / (ρ / 2) ^ 2 = 4 * M / ρ ^ 2 := by
      field_simp
      ring
    linarith
  rw [hfac z, norm_mul, norm_mul]
  calc ‖z - z₁‖ * ‖z - z₂‖ * ‖dslope (dslope f z₁) z₂ z‖
      ≤ ‖z - z₁‖ * ‖z - z₂‖ * (4 * M / ρ ^ 2) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (4 * M / ρ ^ 2) * ‖z - z₁‖ * ‖z - z₂‖ := by ring

end Work.Asymptotics.KaxisMid
