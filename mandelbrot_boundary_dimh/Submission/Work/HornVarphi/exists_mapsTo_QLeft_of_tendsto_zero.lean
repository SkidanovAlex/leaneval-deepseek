import Mathlib
import Submission.Work.Interfaces.HornParts

namespace Work.HornVarphi

open Filter Metric

/-- **Petal avoidance (key step 4 of the HORN-VARPHI route).**

Let `d` be the §4.1 parabolic data of a germ `f₀`, `B ∌ 0` a set, and `G n` holomorphic
sections of `f₀^[n]` over the disc `ball y ρ` (with `0 ∉ ball y ρ`), each `G n` mapping into `B`
and `G n → 0` locally uniformly.  Then for all large `N`, `G N` maps the smaller disc
`closedBall y (ρ/2)` into `φ '' QLeft ξ₀`.

Reason: `G N u` lies in a small ball around `0` which is contained in
`Ωp ∪ φ '' QLeft ξ₀ ∪ {0}` (the field `flower`).  If `G N u ∈ Ωp` then
`u = f₀^[N] (G N u)` has norm `< ρ/2` by uniform convergence of the iterates on `Ωp`, while
`u ∈ closedBall y (ρ/2)` and `0 ∉ ball y ρ` force `ρ/2 ≤ ‖u‖`.  And `G N u ≠ 0` because
`G N u ∈ B` while `0 ∉ B`. -/
theorem exists_mapsTo_QLeft_of_tendsto_zero {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ} (h0B : (0 : ℂ) ∉ B) {y : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hzero : (0 : ℂ) ∉ Metric.ball y ρ) (G : ℕ → ℂ → ℂ) (hhol : ∀ n, DifferentiableOn ℂ (G n) (Metric.ball y ρ)) (hB : ∀ n u, u ∈ Metric.ball y ρ → G n u ∈ B) (hsec : ∀ n u, u ∈ Metric.ball y ρ → f₀^[n] (G n u) = u) (hconv : TendstoLocallyUniformlyOn G (fun _ => 0) Filter.atTop (Metric.ball y ρ)) : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ u ∈ Metric.closedBall y (ρ / 2), G N u ∈ d.φ '' MandelDim.QLeft d.ξ₀ := by
  classical
  have _hhol : ∀ n, DifferentiableOn ℂ (G n) (Metric.ball y ρ) := hhol
  -- a small disc around `0` lying in `Ωp ∪ φ '' QLeft ξ₀ ∪ {0}`
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp d.flower
  -- the iterates of `f₀` tend to `0` uniformly on the petal `Ωp`
  have hΩ : ∀ᶠ N : ℕ in Filter.atTop, ∀ z ∈ d.Ωp, ‖f₀^[N] z‖ < ρ / 2 := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp d.Ωp_unif (ρ / 2) (by linarith)] with N hN z hz
    simpa [dist_eq_norm] using hN z hz
  -- the smaller disc is contained in the disc on which `G` converges
  have hsub : Metric.closedBall y (ρ / 2) ⊆ Metric.ball y ρ := by
    intro x hx
    rw [Metric.mem_closedBall] at hx
    rw [Metric.mem_ball]
    linarith
  -- hence `G` tends to `0` uniformly on `closedBall y (ρ/2)`
  have hU : TendstoUniformlyOn G (fun _ => 0) Filter.atTop (Metric.closedBall y (ρ / 2)) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
        (isCompact_closedBall y (ρ / 2))).mp (hconv.mono hsub)
  have hGcut : ∀ᶠ N : ℕ in Filter.atTop, ∀ u ∈ Metric.closedBall y (ρ / 2), ‖G N u‖ < ε := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hU ε hε] with N hN u hu
    simpa [dist_eq_norm] using hN u hu
  rw [Filter.eventually_atTop] at hΩ hGcut
  obtain ⟨N₁, hN₁⟩ := hΩ
  obtain ⟨N₂, hN₂⟩ := hGcut
  refine ⟨max N₁ N₂, fun N hN u hu => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : N₂ ≤ N := le_trans (le_max_right _ _) hN
  have hu' : u ∈ Metric.ball y ρ := hsub hu
  have hGNB : G N u ∈ B := hB N u hu'
  have hGNε : ‖G N u‖ < ε := hN₂ N hN2 u hu
  have hmem : G N u ∈ d.Ωp ∪ d.φ '' MandelDim.QLeft d.ξ₀ ∪ {0} :=
    hεsub (by rw [Metric.mem_ball]; simpa [dist_eq_norm] using hGNε)
  by_cases hQ : G N u ∈ d.φ '' MandelDim.QLeft d.ξ₀
  · exact hQ
  · exfalso
    rcases hmem with hA | h0
    · rcases hA with hΩp | hQ'
      · -- `G N u ∈ Ωp` is impossible: `u = f₀^[N] (G N u)` would be small, but `‖u‖ ≥ ρ/2`
        have huρ : ρ / 2 ≤ ‖u‖ := by
          have h1 : ρ ≤ dist y 0 := by
            have h := hzero
            rw [Metric.mem_ball] at h
            have h' : ρ ≤ dist (0 : ℂ) y := not_lt.mp h
            simpa [dist_comm] using h'
          have h2 : dist u y ≤ ρ / 2 := Metric.mem_closedBall.mp hu
          have h3 : dist y 0 ≤ dist y u + dist u 0 := dist_triangle y u 0
          rw [dist_comm y u] at h3
          have h4 : dist u 0 = ‖u‖ := by simp [dist_eq_norm]
          linarith [h1, h2, h3, h4]
        have hlt : ‖f₀^[N] (G N u)‖ < ρ / 2 := hN₁ N hN1 (G N u) hΩp
        rw [hsec N u hu'] at hlt
        linarith
      · exact hQ hQ'
    · -- `G N u = 0` is impossible because `G N u ∈ B` and `0 ∉ B`
      rw [Set.mem_singleton_iff] at h0
      rw [h0] at hGNB
      exact h0B hGNB

end Work.HornVarphi
