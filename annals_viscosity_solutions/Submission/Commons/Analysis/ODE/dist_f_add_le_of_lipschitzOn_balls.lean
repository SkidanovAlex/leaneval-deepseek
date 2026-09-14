import Mathlib.Analysis.Normed.Group.Uniform

namespace Commons.Analysis.ODE

set_option autoImplicit false

open Set Metric Filter

/-- Chaining bound: if consecutive "steps" of a sequence `g` are controlled by the increments of a
real sequence `u`, then `dist (g 0) (g N) ≤ C * (u N - u 0)`. -/
private lemma dist_le_mul_sub_of_steps {E : Type*} [PseudoMetricSpace E]
    (g : ℕ → E) (u : ℕ → ℝ) (C : ℝ) (N : ℕ)
    (hstep : ∀ i, i < N → dist (g i) (g (i + 1)) ≤ C * (u (i + 1) - u i)) :
    dist (g 0) (g N) ≤ C * (u N - u 0) := by
  calc dist (g 0) (g N) ≤ ∑ i ∈ Finset.range N, dist (g i) (g (i + 1)) :=
        dist_le_range_sum_dist g N
    _ ≤ ∑ i ∈ Finset.range N, C * (u (i + 1) - u i) :=
        Finset.sum_le_sum (fun i hi => hstep i (Finset.mem_range.mp hi))
    _ = C * ∑ i ∈ Finset.range N, (u (i + 1) - u i) := by rw [Finset.mul_sum]
    _ = C * (u N - u 0) := by rw [Finset.sum_range_sub]

/-- One step of the Lipschitz chain: if `v - u ≥ 0` is at most `(r - ‖W‖)/(B + 1)`, then both
`c u + W` and `c v + W` are within distance `r` of `c u`, so the local Lipschitz bound applies. -/
private lemma step_le_of_lipschitzOn_ball {E : Type*} [NormedAddCommGroup E] {f : E → E}
    {c : ℝ → E} {r K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hc : ∀ s t : ℝ, dist (c s) (c t) ≤ B * |s - t|)
    (hf : ∀ s : ℝ, ∀ x y : E, dist x (c s) ≤ r → dist y (c s) ≤ r →
      dist (f x) (f y) ≤ K * dist x y)
    {W : E} (hW : ‖W‖ < r) {u v : ℝ} (huv : u ≤ v)
    (hv : v - u ≤ (r - ‖W‖) / (B + 1)) :
    dist (f (c u + W)) (f (c v + W)) ≤ K * B * (v - u) := by
  have hrW : 0 < r - ‖W‖ := sub_pos.mpr hW
  have hB1 : 0 < B + 1 := by linarith
  have hvu : 0 ≤ v - u := by linarith
  have habs : |u - v| = v - u := by
    rw [abs_of_nonpos (by linarith : u - v ≤ 0)]; ring
  have hcuv : dist (c u) (c v) ≤ B * (v - u) := by
    simpa only [habs] using hc u v
  -- first point is within the ball of radius `r` around `c u`
  have hmem1 : dist (c u + W) (c u) ≤ r := by
    rw [dist_eq_norm, add_sub_cancel_left]
    linarith [le_of_lt hW]
  -- second point is within the ball of radius `r` around `c u`
  have hmem2 : dist (c v + W) (c u) ≤ r := by
    have htriangle : dist (c v + W) (c u) ≤ ‖W‖ + dist (c v) (c u) := by
      calc dist (c v + W) (c u) ≤ dist (c v + W) (c v) + dist (c v) (c u) :=
            dist_triangle _ _ _
        _ = ‖W‖ + dist (c v) (c u) := by rw [dist_eq_norm, add_sub_cancel_left]
    have hcvu : dist (c v) (c u) ≤ B * (v - u) := by
      have := hc v u
      rwa [abs_of_nonneg hvu] at this
    have hBv : B * (v - u) ≤ B * ((r - ‖W‖) / (B + 1)) :=
      mul_le_mul_of_nonneg_left hv hB
    have hBh : B * ((r - ‖W‖) / (B + 1)) ≤ r - ‖W‖ := by
      rw [← mul_div_assoc, div_le_iff₀ hB1]
      nlinarith [hrW]
    linarith [htriangle, hcvu, hBv, hBh]
  calc dist (f (c u + W)) (f (c v + W))
      ≤ K * dist (c u + W) (c v + W) := hf u (c u + W) (c v + W) hmem1 hmem2
    _ = K * dist (c u) (c v) := by rw [dist_add_right]
    _ ≤ K * (B * (v - u)) := mul_le_mul_of_nonneg_left hcuv hK
    _ = K * B * (v - u) := by ring

/-- **Lipschitz chains along a Lipschitz path.**

Let `f : E → E` be `K`-Lipschitz on every closed ball of radius `r` about the points `c s`
(`s ∈ ℝ`), let `c` be `B`-Lipschitz, and let `W` satisfy `‖W‖ < r`.  Then for `s ≤ t`

`dist (f (c s + W)) (f (c t + W)) ≤ K * B * (t - s)`.

Proof sketch: let `h := (r - ‖W‖) / (B + 1) > 0` and split the interval `[s,t]` into `N` equal
pieces (`N` large enough that each piece has length `≤ h`).  On one piece with endpoints `u ≤ v`
both points `c u + W` and `c v + W` lie in the closed ball of radius `r` about `c u`, because
`dist (c v + W) (c u) ≤ ‖c v - c u‖ + ‖W‖ ≤ B * (v - u) + ‖W‖ ≤ (r - ‖W‖) + ‖W‖ = r`; hence
`dist (f (c u + W)) (f (c v + W)) ≤ K * ‖c u - c v‖ ≤ K * B * (v - u)`.  Summing these
inequalities over the pieces (triangle inequality for `dist`) gives the claim, using
`∑ (v_i - u_i) = t - s`. -/
theorem dist_f_add_le_of_lipschitzOn_balls
    {E : Type*} [NormedAddCommGroup E] {f : E → E} {c : ℝ → E} {r K B : ℝ}
    (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hc : ∀ s t : ℝ, dist (c s) (c t) ≤ B * |s - t|)
    (hf : ∀ s : ℝ, ∀ x y : E, dist x (c s) ≤ r → dist y (c s) ≤ r →
      dist (f x) (f y) ≤ K * dist x y)
    {W : E} (hW : ‖W‖ < r) {s t : ℝ} (hst : s ≤ t) :
    dist (f (c s + W)) (f (c t + W)) ≤ K * B * (t - s) := by
  by_cases hst' : s = t
  · subst hst'
    simp
  · have hrW : 0 < r - ‖W‖ := sub_pos.mpr hW
    have hB1 : 0 < B + 1 := by linarith
    set h : ℝ := (r - ‖W‖) / (B + 1) with hh_def
    have hh : 0 < h := div_pos hrW hB1
    obtain ⟨N, hN⟩ := exists_nat_gt ((t - s) / h)
    have hNpos : (0 : ℝ) < (N : ℝ) :=
      lt_of_le_of_lt (div_nonneg (by linarith) (le_of_lt hh)) hN
    have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
    have hNh : t - s < (N : ℝ) * h := by
      rw [div_lt_iff₀ hh] at hN; linarith
    have hstep_h : (t - s) / (N : ℝ) ≤ h := by
      rw [div_le_iff₀ hNpos]; nlinarith
    set d : ℝ := (t - s) / (N : ℝ) with hd_def
    have hd_nonneg : 0 ≤ d := by rw [hd_def]; positivity
    have hd_le : d ≤ h := by rw [hd_def]; exact hstep_h
    let φ : ℕ → ℝ := fun i => s + (i : ℝ) * d
    let g : ℕ → E := fun i => f (c (φ i) + W)
    have hφstep : ∀ i : ℕ, φ (i + 1) - φ i = d := by
      intro i; simp only [φ]; push_cast; ring
    have hφ0 : φ 0 = s := by simp only [φ]; ring
    have hφN : φ N = t := by
      have hNd : (N : ℝ) * d = t - s := by
        rw [hd_def, mul_comm]; exact div_mul_cancel₀ _ hNne
      simp only [φ]; rw [hNd]; ring
    have hstep : ∀ i, i < N → dist (g i) (g (i + 1)) ≤ K * B * (φ (i + 1) - φ i) := by
      intro i _
      have huv : φ i ≤ φ (i + 1) := by linarith [hφstep i, hd_nonneg]
      have hv : φ (i + 1) - φ i ≤ (r - ‖W‖) / (B + 1) := by
        rw [hφstep i]; exact hd_le
      exact step_le_of_lipschitzOn_ball hK hB hc hf hW huv hv
    have hchain := dist_le_mul_sub_of_steps g φ (K * B) N hstep
    have hg0 : g 0 = f (c s + W) := by simp only [g]; rw [hφ0]
    have hgN : g N = f (c t + W) := by simp only [g]; rw [hφN]
    rw [hg0, hgN, hφ0, hφN] at hchain
    exact hchain

end Commons.Analysis.ODE