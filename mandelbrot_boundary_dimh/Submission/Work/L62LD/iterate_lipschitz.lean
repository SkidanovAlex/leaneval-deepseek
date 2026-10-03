import Mathlib

/-!
# L62LD — iterates of a holomorphic map are `Δ^N`-Lipschitz along a `K`-orbit

If `K` has a `δ`-neighbourhood contained in the open set `O`, `F` is holomorphic on `O` and
`‖deriv F‖ ≤ Δ` on the `δ`-neighbourhood of `K`, then for any `N` and any `p` whose orbit up to
time `N` stays in `K`, the `N`-th iterates of `F` satisfy

`‖F^[N] p - F^[N] q‖ ≤ Δ^N * ‖p - q‖`

provided the two orbits stay within `δ` of each other, which is guaranteed by the hypothesis
`‖p - q‖ * Δ^N ≤ δ`.  This is the elementary Lipschitz estimate used for the drift/chain analysis
of the lower-end head of Lemma 6.2.
-/

namespace Work.L62LD

theorem iterate_lipschitz {F : ℂ → ℂ} {K O : Set ℂ} {Δ δ : ℝ}
    (hδ : 0 < δ) (hΔ : 1 ≤ Δ) (hO : IsOpen O)
    (hKδ : ∀ v ∈ K, ∀ z : ℂ, ‖z‖ ≤ δ → v + z ∈ O)
    (hFd : DifferentiableOn ℂ F O)
    (hbd : ∀ v ∈ K, ∀ z : ℂ, ‖z‖ ≤ δ → ‖deriv F (v + z)‖ ≤ Δ) :
    ∀ (N : ℕ) (p q : ℂ), (∀ n, n < N → (F^[n]) p ∈ K) →
      ‖p - q‖ * Δ ^ N ≤ δ → ‖(F^[N]) p - (F^[N]) q‖ ≤ Δ ^ N * ‖p - q‖ := by
  have _ := hδ
  -- the one-step estimate: the mean value inequality on the segment `[x, y] ⊆ O`
  have hstep : ∀ x ∈ K, ∀ y : ℂ, ‖y - x‖ ≤ δ → ‖F y - F x‖ ≤ Δ * ‖y - x‖ := by
    intro x hx y hy
    have hdx : ∀ u ∈ segment ℝ x y, ‖u - x‖ ≤ δ := by
      intro u hu
      have h2 : ‖u - x‖ ≤ ‖x - y‖ := by
        have h3 : dist u x ≤ dist x y := by
          rw [← Metric.mem_closedBall]; exact segment_subset_closedBall_left x y hu
        rwa [dist_eq_norm, dist_eq_norm] at h3
      calc ‖u - x‖ ≤ ‖x - y‖ := h2
        _ = ‖y - x‖ := norm_sub_rev _ _
        _ ≤ δ := hy
    have hmem : ∀ u ∈ segment ℝ x y, u ∈ O := by
      intro u hu
      simpa using hKδ x hx (u - x) (hdx u hu)
    have hdiff : ∀ u ∈ segment ℝ x y, DifferentiableAt ℂ F u := fun u hu =>
      hFd.differentiableAt (hO.mem_nhds (hmem u hu))
    have hbound : ∀ u ∈ segment ℝ x y, ‖deriv F u‖ ≤ Δ := by
      intro u hu
      simpa using hbd x hx (u - x) (hdx u hu)
    exact Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound (convex_segment x y)
      (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  intro N p q hp hpq
  have hmain : ∀ k ≤ N, ‖(F^[k]) p - (F^[k]) q‖ ≤ Δ ^ k * ‖p - q‖ := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
        intro hk
        have hkN : k ≤ N := le_trans (Nat.le_succ k) hk
        have hkd : ‖(F^[k]) p - (F^[k]) q‖ ≤ δ := by
          have h2 : Δ ^ k * ‖p - q‖ ≤ Δ ^ N * ‖p - q‖ :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hΔ hkN) (norm_nonneg _)
          calc ‖(F^[k]) p - (F^[k]) q‖ ≤ Δ ^ k * ‖p - q‖ := ih hkN
            _ ≤ Δ ^ N * ‖p - q‖ := h2
            _ = ‖p - q‖ * Δ ^ N := by ring
            _ ≤ δ := hpq
        have hkK : (F^[k]) p ∈ K := hp k (Nat.lt_of_succ_le hk)
        have hs := hstep ((F^[k]) p) hkK ((F^[k]) q) (by rw [norm_sub_rev]; exact hkd)
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        calc ‖F ((F^[k]) p) - F ((F^[k]) q)‖
            = ‖F ((F^[k]) q) - F ((F^[k]) p)‖ := norm_sub_rev _ _
          _ ≤ Δ * ‖(F^[k]) q - (F^[k]) p‖ := hs
          _ = Δ * ‖(F^[k]) p - (F^[k]) q‖ := by rw [norm_sub_rev]
          _ ≤ Δ * (Δ ^ k * ‖p - q‖) :=
              mul_le_mul_of_nonneg_left (ih hkN) (le_trans zero_le_one hΔ)
          _ = Δ ^ (k + 1) * ‖p - q‖ := by rw [pow_succ]; ring
  exact hmain N le_rfl

end Work.L62LD
