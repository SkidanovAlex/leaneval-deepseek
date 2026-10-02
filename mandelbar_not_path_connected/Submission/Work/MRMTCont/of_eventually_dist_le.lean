import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Uniformity

namespace Work.MRMTCont

/-- If `F n` converges locally uniformly to `f`, and `G n` is eventually uniformly close to
`F n` on the discs `‖z‖ ≤ n` with error tending to `0`, then `G n` converges locally uniformly
to `f` as well. -/
theorem of_eventually_dist_le {F G : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {a : ℕ → ℝ}
    (hF : TendstoLocallyUniformly F f Filter.atTop) (ha : Filter.Tendsto a Filter.atTop (nhds 0))
    (hclose : ∀ᶠ j : ℕ in Filter.atTop, ∀ z : ℂ, ‖z‖ ≤ (j : ℝ) → dist (G j z) (F j z) ≤ a j) :
    TendstoLocallyUniformly G f Filter.atTop := by
  intro u hu x
  rw [Metric.mem_uniformity_dist] at hu
  obtain ⟨ε, hε, hu⟩ := hu
  have hu' : {p : ℂ × ℂ | dist p.1 p.2 < ε / 2} ∈ 𝓤 ℂ :=
    Metric.dist_mem_uniformity (half_pos hε)
  obtain ⟨t, ht, htev⟩ := hF _ hu' x
  have E4 : ∀ᶠ n : ℕ in Filter.atTop, (⌈‖x‖ + 1⌉₊ : ℝ) ≤ (n : ℝ) :=
    Filter.eventually_atTop.mpr ⟨⌈‖x‖ + 1⌉₊, fun n hn => by exact_mod_cast hn⟩
  refine ⟨t ∩ Metric.ball x 1, Filter.inter_mem ht ?_, ?_⟩
  · exact Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos)
  · filter_upwards [htev, hclose, (tendsto_order.1 ha).2 (ε / 2) (half_pos hε), E4]
      with n h1 h2 h3 h4 y hy
    have hyt : y ∈ t := hy.1
    have hyball : y ∈ Metric.ball x 1 := hy.2
    have hyx : dist y x < 1 := Metric.mem_ball.mp hyball
    have hynorm : ‖y‖ ≤ (n : ℝ) := by
      have hlt : ‖y‖ < ‖x‖ + 1 := by
        calc ‖y‖ = ‖y - x + x‖ := by rw [sub_add_cancel]
          _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
          _ = dist y x + ‖x‖ := by rw [dist_eq_norm]
          _ < 1 + ‖x‖ := by linarith
          _ = ‖x‖ + 1 := by ring
      have hN : ‖x‖ + 1 ≤ (⌈‖x‖ + 1⌉₊ : ℝ) := Nat.le_ceil _
      exact (hlt.trans_le (hN.trans h4)).le
    have hFy : dist (f y) (F n y) < ε / 2 := h1 y hyt
    have hG : dist (F n y) (G n y) < ε / 2 := by
      have := h2 y hynorm
      rw [dist_comm] at this
      exact lt_of_le_of_lt this h3
    have hdist : dist (f y) (G n y) < ε := by
      calc dist (f y) (G n y) ≤ dist (f y) (F n y) + dist (F n y) (G n y) :=
            dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := add_lt_add hFy hG
        _ = ε := by ring
    exact hu hdist

end Work.MRMTCont
