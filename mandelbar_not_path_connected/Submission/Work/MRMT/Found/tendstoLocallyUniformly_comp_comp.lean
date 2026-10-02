import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

open Filter Topology

/-- **Composition of locally uniformly convergent families.**

If `F n → φ` and `G n → γ` locally uniformly on `ℂ`, with `φ` and `γ` continuous, then
`F n ∘ G n → φ ∘ γ` locally uniformly.

The proof uses that `ℂ` is locally compact: on a neighbourhood of `x` the values `G n y`
eventually lie in a fixed closed ball `B` containing `γ` of a neighbourhood of `x`; `φ` is
uniformly continuous on `B` by Heine--Cantor and `F n → φ` uniformly on the compact ball `B`. -/
theorem tendstoLocallyUniformly_comp_comp {F : ℕ → ℂ → ℂ} {φ : ℂ → ℂ} {G : ℕ → ℂ → ℂ} {γ : ℂ → ℂ}
    (hF : TendstoLocallyUniformly F φ Filter.atTop) (hG : TendstoLocallyUniformly G γ Filter.atTop)
    (hφ : Continuous φ) (hγ : Continuous γ) :
    TendstoLocallyUniformly (fun n => F n ∘ G n) (φ ∘ γ) Filter.atTop := by
  rw [Metric.tendstoLocallyUniformly_iff] at hG ⊢
  intro ε hε x
  have hε2 : 0 < ε / 2 := by linarith
  -- `γ` is bounded on a neighbourhood of `x`
  obtain ⟨r, hr⟩ : ∃ r : ℝ, γ '' Metric.closedBall x 1 ⊆ Metric.closedBall (0 : ℂ) r :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp
      (((isCompact_closedBall x (1 : ℝ)).image hγ).isBounded)
  -- `φ` is uniformly continuous on the compact ball of radius `r + 1`
  have huc : UniformContinuousOn φ (Metric.closedBall (0 : ℂ) (r + 1)) :=
    (isCompact_closedBall (0 : ℂ) (r + 1)).uniformContinuousOn_of_continuous hφ.continuousOn
  obtain ⟨δ, hδ0, hδ⟩ := (Metric.uniformContinuousOn_iff.mp huc) (ε / 2) hε2
  -- `F n → φ` uniformly on the compact ball of radius `r + 1`
  have hFB : TendstoUniformlyOn F φ Filter.atTop (Metric.closedBall (0 : ℂ) (r + 1)) :=
    (tendstoLocallyUniformly_iff_forall_isCompact.mp hF) _
      (isCompact_closedBall (0 : ℂ) (r + 1))
  have hFend : ∀ᶠ n in Filter.atTop, ∀ w ∈ Metric.closedBall (0 : ℂ) (r + 1),
      dist (φ w) (F n w) < ε / 2 :=
    (Metric.tendstoUniformlyOn_iff.mp hFB) (ε / 2) hε2
  obtain ⟨t, ht, htend⟩ := hG (min δ 1) (lt_min hδ0 one_pos) x
  refine ⟨t ∩ Metric.ball x 1, Filter.inter_mem ht (Metric.ball_mem_nhds x one_pos), ?_⟩
  filter_upwards [htend, hFend] with n hn hFn y hy
  obtain ⟨hyt, hyb⟩ := hy
  simp only [Function.comp_apply]
  have hdl : dist (γ y) (G n y) < min δ 1 := hn y hyt
  have hdδ : dist (γ y) (G n y) < δ := lt_of_lt_of_le hdl (min_le_left _ _)
  have hgy_mem : γ y ∈ Metric.closedBall (0 : ℂ) (r + 1) := by
    have h := hr ⟨y, Metric.ball_subset_closedBall hyb, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    linarith
  have hGy_mem : G n y ∈ Metric.closedBall (0 : ℂ) (r + 1) := by
    have h1 : ‖G n y - γ y‖ < 1 := by
      have h := lt_of_lt_of_le hdl (min_le_right _ _)
      rwa [dist_comm, dist_eq_norm] at h
    have h2 : ‖γ y‖ ≤ r := by
      have h := hr ⟨y, Metric.ball_subset_closedBall hyb, rfl⟩
      rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
    have h3 : ‖G n y‖ ≤ ‖G n y - γ y‖ + ‖γ y‖ := by
      simpa using norm_add_le (G n y - γ y) (γ y)
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    linarith
  have h1 : dist (φ (γ y)) (φ (G n y)) < ε / 2 := hδ (γ y) hgy_mem (G n y) hGy_mem hdδ
  have h2 : dist (φ (G n y)) (F n (G n y)) < ε / 2 := hFn (G n y) hGy_mem
  calc dist (φ (γ y)) (F n (G n y))
      ≤ dist (φ (γ y)) (φ (G n y)) + dist (φ (G n y)) (F n (G n y)) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add h1 h2
    _ = ε := by ring

end Work.MRMT.Found
