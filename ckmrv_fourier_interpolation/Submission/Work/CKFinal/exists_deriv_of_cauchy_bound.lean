import Mathlib

namespace Work.CKFinal

open Filter Topology

/-- Quantitative Cauchy criterion for differentiability at a point of `ℝ → ℂ`: if the difference
quotients at `r` are close whenever the steps are close, then `f` is differentiable at `r` and the
quantitative bound passes to the limit. -/
lemma exists_deriv_of_cauchy_bound {f : ℝ → ℂ} {r D0 S : ℝ} (hD0 : 0 ≤ D0) (hS : 0 ≤ S)
    (hbd : ∀ a b : ℝ, a ≠ 0 → b ≠ 0 →
      ‖(f (r + a) - f r) / a - (f (r + b) - f r) / b‖ ≤ D0 * (|a| + |b|) * S) :
    ∃ D : ℂ, HasDerivAt f D r ∧
      ∀ a : ℝ, a ≠ 0 → ‖(f (r + a) - f r) / a - D‖ ≤ D0 * |a| * S := by
  -- A step small enough that the oscillation bound is below `ε`.
  have hdelta : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, D0 * (δ + δ) * S < ε := by
    intro ε hε
    have h1 : (0:ℝ) < D0 * S + 1 := by positivity
    refine ⟨ε / (2 * (D0 * S + 1)), by positivity, ?_⟩
    have hratio : D0 * S / (D0 * S + 1) < 1 := by
      rw [div_lt_one h1]; linarith
    calc D0 * (ε / (2 * (D0 * S + 1)) + ε / (2 * (D0 * S + 1))) * S
        = ε * (D0 * S / (D0 * S + 1)) := by field_simp; ring
      _ < ε * 1 := mul_lt_mul_of_pos_left hratio hε
      _ = ε := by ring
  set g : ℝ → ℂ := fun a => (f (r + a) - f r) / a with hg
  -- The difference-quotient function is Cauchy along the sequence of steps `1/(n+1) → 0`.
  set a : ℕ → ℝ := fun n => ((n:ℝ) + 1)⁻¹ with ha
  have ha_ne : ∀ n, a n ≠ 0 := by
    intro n; rw [ha]; positivity
  have ha_tendsto : Tendsto a atTop (𝓝 0) := by
    rw [ha]
    exact tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hosc : ∀ u v : ℝ, u ≠ 0 → v ≠ 0 → dist (g u) (g v) ≤ D0*(|u|+|v|)*S := by
    intro u v hu hv
    rw [hg, dist_eq_norm]
    simpa using hbd u v hu hv
  have hcauchy : CauchySeq (fun n => g (a n)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨δ, hδpos, hδ⟩ := hdelta ε hε
    have hev : ∀ᶠ n in atTop, |a n| < δ := by
      have h1 := ha_tendsto.eventually (Metric.ball_mem_nhds (0:ℝ) hδpos)
      filter_upwards [h1] with n hn
      rwa [Real.dist_eq, sub_zero] at hn
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
    refine ⟨N, fun m hm n hn => ?_⟩
    have hm' : |a m| < δ := hN m hm
    have hn' : |a n| < δ := hN n hn
    calc dist (g (a m)) (g (a n)) ≤ D0 * (|a m| + |a n|) * S := hosc _ _ (ha_ne m) (ha_ne n)
      _ < ε := by
        have hx : |a m| + |a n| < δ + δ := by linarith
        have hK : 0 ≤ D0 * S := mul_nonneg hD0 hS
        calc D0 * (|a m| + |a n|) * S = (D0*S) * (|a m| + |a n|) := by ring
          _ ≤ (D0*S) * (δ + δ) := mul_le_mul_of_nonneg_left (le_of_lt hx) hK
          _ = D0 * (δ + δ) * S := by ring
          _ < ε := hδ
  obtain ⟨D, hD⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- The limit satisfies the quantitative bound, by passing to the limit in `b`.
  have hbound : ∀ u : ℝ, u ≠ 0 → ‖g u - D‖ ≤ D0 * |u| * S := by
    intro u hu
    have hcont : Continuous (fun x : ℝ => D0 * (|u| + |x|) * S) := by fun_prop
    have hb : Tendsto (fun n : ℕ => ‖g u - g (a n)‖) atTop (𝓝 ‖g u - D‖) :=
      (tendsto_const_nhds.sub hD).norm
    have hc : Tendsto (fun n : ℕ => D0 * (|u| + |a n|) * S) atTop
        (𝓝 (D0 * (|u| + |(0:ℝ)|) * S)) := (hcont.tendsto 0).comp ha_tendsto
    have h3 := le_of_tendsto_of_tendsto hb hc
      (Filter.Eventually.of_forall (fun n => by
        show ‖g u - g (a n)‖ ≤ D0 * (|u| + |a n|) * S
        rw [← dist_eq_norm]; exact hosc u (a n) hu (ha_ne n)))
    simpa using h3
  -- The quantitative bound forces convergence of the difference quotients to `D`.
  have hmain : Tendsto g (𝓝[≠] 0) (𝓝 D) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hcont : Continuous (fun x : ℝ => D0 * |x| * S) := by fun_prop
    have hbdd : Tendsto (fun x : ℝ => D0 * |x| * S) (𝓝[≠] 0) (𝓝 0) := by
      have hid : Tendsto (fun x : ℝ => x) (𝓝[≠] 0) (𝓝 (0:ℝ)) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have h2 : Tendsto (fun x : ℝ => D0 * |x| * S) (𝓝[≠] 0) (𝓝 (D0 * |(0:ℝ)| * S)) :=
        (hcont.tendsto 0).comp hid
      simpa using h2
    refine squeeze_zero' ?_ ?_ hbdd
    · filter_upwards with x; exact norm_nonneg _
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact hbound x hx
  refine ⟨D, ?_, ?_⟩
  · rw [hasDerivAt_iff_tendsto_slope_zero]
    refine Tendsto.congr (fun t => ?_) hmain
    rw [hg]
    simp [Complex.real_smul, div_eq_mul_inv, mul_comm]
  · intro u hu
    simpa [hg] using hbound u hu

end Work.CKFinal
