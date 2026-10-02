import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open Filter Asymptotics Set
open scoped Topology
/-- A curve `γ`, continuous on `(0,1]` and tending to `0` at `0⁺`, which is carried into itself by
`σ` (i.e. `σ t ∈ (0,1]` for every `t ∈ (0,1]`, `t = 1` included) with a strict decrease of the norm,
forces `σ t → 0` as `t → 0⁺`.
Hint: `t = 1 ∈ Ioc 0 1` and `hσm` give `σ 1 > 0`, so the strict decrease forces `γ t ≠ 0` for every
`t ∈ (0,1]`. If `σ` did not tend to `0`, some sequence `tₙ → 0⁺` would have `σ tₙ ≥ ε > 0`, hence
`‖γ (σ tₙ)‖ ≥ min_{[ε,1]} ‖γ‖ > 0` (compactness + nonvanishing), contradicting
`‖γ (σ tₙ)‖ < ‖γ tₙ‖ → 0`. -/
theorem tendsto_sigma_zero {γ : ℝ → ℂ} {σ : ℝ → ℝ}
    (hγc : ContinuousOn γ (Set.Ioc 0 1)) (hγt : Filter.Tendsto γ (𝓝[>] (0:ℝ)) (𝓝 0))
    (hσm : ∀ t ∈ Set.Ioc (0:ℝ) 1, σ t ∈ Set.Ioc (0:ℝ) 1)
    (hdec : ∀ t ∈ Set.Ioc (0:ℝ) 1, ‖γ (σ t)‖ < ‖γ t‖) :
    Filter.Tendsto σ (𝓝[>] (0:ℝ)) (𝓝 0) := by
  -- `γ` is nonzero on `(0,1]`: the strict decrease at `t` has `‖γ t‖ > ‖γ (σ t)‖ ≥ 0`.
  have hγne : ∀ t ∈ Ioc (0:ℝ) 1, γ t ≠ 0 := by
    intro t ht
    exact norm_ne_zero_iff.mp (ne_of_gt (lt_of_le_of_lt (norm_nonneg _) (hdec t ht)))
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- We prove `σ t < min ε 1` eventually; `min ε 1 = ε₀ ∈ (0,1]` so `[ε₀,1] ⊆ (0,1]`.
  set ε₀ : ℝ := min ε 1 with hε₀
  have hε₀pos : 0 < ε₀ := by rw [hε₀]; exact lt_min hε zero_lt_one
  have hε₀le : ε₀ ≤ 1 := by rw [hε₀]; exact min_le_right _ _
  -- `m = infDist 0 (γ '' [ε₀,1]) > 0`: the compact image `γ '' [ε₀,1]` avoids `0`.
  set m : ℝ := Metric.infDist (0:ℂ) (γ '' (Icc ε₀ 1)) with hm
  have hKne : (Icc ε₀ 1 : Set ℝ).Nonempty := ⟨ε₀, le_rfl, hε₀le⟩
  have hKsub : (Icc ε₀ 1 : Set ℝ) ⊆ Ioc (0:ℝ) 1 :=
    fun x hx => ⟨lt_of_lt_of_le hε₀pos hx.1, hx.2⟩
  have h0not : (0:ℂ) ∉ γ '' (Icc ε₀ 1) := by
    rintro ⟨x, hx, hx0⟩
    exact hγne x (hKsub hx) hx0
  have hmpos : 0 < m := by
    rw [hm]
    exact ((isCompact_Icc.image_of_continuousOn (hγc.mono hKsub)).isClosed.notMem_iff_infDist_pos
      (hKne.image γ)).1 h0not
  -- Eventually `‖γ t‖ < m`, since `γ t → 0`.
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), ‖γ t‖ < m := by
    have hball : Metric.ball (0:ℂ) m ∈ 𝓝 (0:ℂ) := Metric.ball_mem_nhds 0 hmpos
    filter_upwards [hγt hball] with t ht
    simp only [mem_preimage, Metric.mem_ball, dist_eq_norm, sub_zero] at ht
    exact ht
  filter_upwards [hev, self_mem_nhdsWithin,
    (eventually_lt_nhds (show (0:ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
    with t htnorm ht0 ht1
  have ht : t ∈ Ioc (0:ℝ) 1 := ⟨ht0, le_of_lt ht1⟩
  have hσt : σ t ∈ Ioc (0:ℝ) 1 := hσm t ht
  -- `σ t < ε₀`: otherwise `σ t ∈ [ε₀,1]`, so `m ≤ ‖γ (σ t)‖ < ‖γ t‖ < m`.
  have hlt : σ t < ε₀ := by
    by_contra hcon
    have hσin : σ t ∈ Icc ε₀ 1 := ⟨not_lt.mp hcon, hσt.2⟩
    have hle2 : m ≤ ‖γ (σ t)‖ := by
      rw [hm]
      have hmem : γ (σ t) ∈ γ '' (Icc ε₀ 1) := ⟨σ t, hσin, rfl⟩
      have := Metric.infDist_le_dist_of_mem (x := (0:ℂ)) hmem
      rwa [dist_eq_norm, zero_sub, norm_neg] at this
    have hd := hdec t ht
    linarith
  rw [dist_eq_norm, sub_zero, Real.norm_eq_abs, abs_of_pos hσt.1]
  exact lt_of_lt_of_le hlt (by rw [hε₀]; exact min_le_left _ _)

end Work.LandLeaves
