import Mathlib
import Submission.Lib.Unif2.Commons.Analysis.Complex.exists_ball_factorization_of_analyticAt_zero

namespace Work.Fatou.Analysis

lemma analyticOrderLowerBound (G : ℂ → ℂ) (hG : Differentiable ℂ G)
    (hne : ∀ w : ℂ, w ≠ 0 → G w ≠ 0) :
    ∃ (n : ℕ) (c R : ℝ), 0 < c ∧ 0 < R ∧
      ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ ≤ R → c * ‖w‖ ^ n ≤ ‖G w‖ := by
  by_cases h0 : G 0 = 0
  · -- Case 1: `G` vanishes at `0`.  Since `G` is entire and non-zero away from `0`, it is not
    -- locally zero at `0` (identity principle), so it has a zero of finite order `k` there.
    have hnc : ¬ Filter.Eventually (fun z : ℂ => G z = 0) (nhds 0) := by
      intro hev
      have hEqOn : Set.EqOn G 0 Set.univ :=
        AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
          (f := G) (U := Set.univ) (fun z _ => hG.analyticAt z) isPreconnected_univ
          (Set.mem_univ 0) hev
      have h1 : G 1 = 0 := hEqOn (Set.mem_univ 1)
      exact hne 1 (by norm_num) h1
    -- Factor `G z = z ^ k * ψ z` near `0`, with `ψ` analytic and non-vanishing there.
    obtain ⟨R₀, k, ψ, hR₀pos, _hR₀lt, _hk1, hψan, hψne, hfact⟩ :=
      Commons.Analysis.Complex.exists_ball_factorization_of_analyticAt_zero
        (f := G) (c := 0) (ρ := 1) zero_lt_one (hG.analyticAt 0) h0 hnc
    have hψ0an : AnalyticAt ℂ ψ 0 := hψan 0 (Metric.mem_ball_self hR₀pos)
    have hψ0ne : ψ 0 ≠ 0 := hψne 0 (Metric.mem_ball_self hR₀pos)
    have hψ0pos : 0 < ‖ψ 0‖ := norm_pos_iff.mpr hψ0ne
    -- `ψ` is bounded below near `0` by half of `‖ψ 0‖`.
    obtain ⟨δ, hδpos, hδ⟩ :=
      Metric.continuousAt_iff.mp hψ0an.continuousAt (‖ψ 0‖ / 2) (half_pos hψ0pos)
    refine ⟨k, ‖ψ 0‖ / 2, min R₀ δ / 2, half_pos hψ0pos,
      div_pos (lt_min hR₀pos hδpos) two_pos, ?_⟩
    intro w hwpos hwR
    have hR_lt_R₀ : min R₀ δ / 2 < R₀ := by
      have h1 : min R₀ δ ≤ R₀ := min_le_left _ _
      linarith
    have hR_lt_δ : min R₀ δ / 2 < δ := by
      have h1 : min R₀ δ ≤ δ := min_le_right _ _
      linarith
    have hwR₀ : w ∈ Metric.ball (0 : ℂ) R₀ := by
      rw [Metric.mem_ball, dist_zero_right]; linarith
    have hwd : dist w (0 : ℂ) < δ := by
      rw [dist_zero_right]; linarith
    have hψw : ‖ψ 0‖ / 2 < ‖ψ w‖ := by
      have h1 : dist (ψ w) (ψ 0) < ‖ψ 0‖ / 2 := hδ (x := w) hwd
      rw [dist_eq_norm] at h1
      have h2 : ‖ψ 0‖ - ‖ψ w‖ ≤ ‖ψ w - ψ 0‖ := by
        have h3 := norm_sub_norm_le (ψ 0) (ψ w)
        rwa [norm_sub_rev] at h3
      linarith
    have hfactw : G w = w ^ k * ψ w := by
      simpa using hfact w hwR₀
    rw [hfactw, norm_mul, norm_pow]
    have hnn : 0 ≤ ‖w‖ ^ k := pow_nonneg (norm_nonneg w) k
    calc ‖ψ 0‖ / 2 * ‖w‖ ^ k = ‖w‖ ^ k * (‖ψ 0‖ / 2) := by ring
      _ ≤ ‖w‖ ^ k * ‖ψ w‖ := mul_le_mul_of_nonneg_left (le_of_lt hψw) hnn
  · -- Case 2: `G 0 ≠ 0`.  Then `‖G‖` is bounded below near `0` by continuity.
    have hG0pos : 0 < ‖G 0‖ := norm_pos_iff.mpr h0
    obtain ⟨δ, hδpos, hδ⟩ :=
      Metric.continuousAt_iff.mp (hG.analyticAt 0).continuousAt (‖G 0‖ / 2) (half_pos hG0pos)
    refine ⟨0, ‖G 0‖ / 2, δ / 2, half_pos hG0pos, by linarith, ?_⟩
    intro w _hwpos hwR
    have hwd : dist w (0 : ℂ) < δ := by
      rw [dist_zero_right]; linarith
    have h1 : dist (G w) (G 0) < ‖G 0‖ / 2 := hδ (x := w) hwd
    rw [dist_eq_norm] at h1
    have h2 : ‖G 0‖ - ‖G w‖ ≤ ‖G w - G 0‖ := by
      have h3 := norm_sub_norm_le (G 0) (G w)
      rwa [norm_sub_rev] at h3
    simp only [pow_zero, mul_one]
    linarith

end Work.Fatou.Analysis
