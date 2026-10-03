import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Repel.Setup

/-!
# REPEL: `chain_setup_v4` — the chain data with `ρ` small enough for BOTH starting points

`Work.Repel.chain_setup_v2` chooses the Lemma-6.2 radius `ρ` so that `closedBall ζa (2ρ) ⊆ d₁.Dφ`.
The §6 assembly passes the compact `K' = closedBall ζa (2ρ) ∪ closedBall ζb (2ρ)` to the level-1
`PertStatement` call (it must contain the whole base disc of the chain, whichever of the two
starting points Lemma 6.2 selects), so it needs the same inclusion for `ζb`.
-/

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology

/-- **Lemma 6.2 chain data with `ρ` small enough for both `ζa` and `ζb`.** -/
theorem chain_setup_v4 (hL62 : MandelDim.L62Statement) (S : Work.Repel.Setup) (b : ℝ) (hb : 0 < b)
    (hζa : S.ζa ∈ S.d₁.Dφ) (hζb : S.ζb ∈ S.d₁.Dφ)
    (ρmax : ℝ) (hρmax : 0 < ρmax) :
    ∃ CS : Work.Repel.ChainSetup S b, CS.ρ ≤ ρmax ∧
      Metric.closedBall S.ζa (2 * CS.ρ) ∪ Metric.closedBall S.ζb (2 * CS.ρ) ⊆ S.d₁.Dφ := by
  -- balls around `ζa` and `ζb` contained in the open set `d₁.Dφ`
  obtain ⟨εa, hεapos, hεa⟩ := Metric.mem_nhds_iff.mp (S.d₁.Dφ_open.mem_nhds hζa)
  obtain ⟨εb, hεbpos, hεb⟩ := Metric.mem_nhds_iff.mp (S.d₁.Dφ_open.mem_nhds hζb)
  -- Lemma 6.2 at the level-1 germ gives a threshold `ρ₀ > 0`
  obtain ⟨ρ₀, hρ₀pos, hρ₀⟩ :=
    hL62 (g0germ S.d₀) (Dg0germ S.d₀ S.hd₀) (inF0_g0germ S.d₀ S.hd₀) S.d₁ S.hd₁ b hb
      S.ζa S.ζb S.hζa S.hζb S.hdisj
  -- choose the chain radius small enough to fit inside both openness balls
  set ρ : ℝ := min ρ₀ (min (min εa εb / 4) ρmax) with hρdef
  have hρpos : 0 < ρ := lt_min hρ₀pos (lt_min (by positivity) hρmax)
  have hρle : ρ ≤ ρ₀ := min_le_left ρ₀ (min (min εa εb / 4) ρmax)
  have hρle' : ρ ≤ min εa εb / 4 := le_trans (min_le_right ρ₀ _) (min_le_left _ _)
  have hρmax : ρ ≤ ρmax := le_trans (min_le_right ρ₀ _) (min_le_right _ _)
  have hρa : ρ ≤ εa / 4 := le_trans hρle' (by linarith [min_le_left εa εb])
  have hρb : ρ ≤ εb / 4 := le_trans hρle' (by linarith [min_le_right εa εb])
  obtain ⟨K, hKc, hKsub, y₁, δ, C₀, C₁, C₁', hy₁, hδ, hC₁, hchain⟩ := hρ₀ ρ hρpos hρle
  refine ⟨{ ρ := ρ, hρ := hρpos, K₂ := K, hK₂c := hKc, hK₂sub := hKsub, y₁ := y₁,
            hy₁ := hy₁, δ := δ, hδ := hδ, C₀ := C₀, C₁ := C₁, C₁' := C₁', hC₁ := hC₁,
            chain := ?_ }, hρmax, ?_⟩
  · intro R DR hDR hT hdiff hsub hclose β hβre₀ hβre₁ hβim
    obtain ⟨W, s, hs, hW0, hopen, hch, hdisj, hmarch, hbnd, hcl, hder⟩ :=
      hchain R DR hDR hT hdiff hsub hclose β hβre₀ hβre₁ hβim
    exact ⟨W, s, ⟨hs, hW0, hopen, hch, hdisj, hmarch, hbnd, hcl, hder⟩⟩
  · intro z hz
    rcases hz with hz | hz
    · rw [Metric.mem_closedBall] at hz
      have h2 : (2 : ℝ) * ρ ≤ εa / 2 := by linarith
      have h1 : dist z S.ζa < εa := by linarith
      exact hεa (by rwa [Metric.mem_ball])
    · rw [Metric.mem_closedBall] at hz
      have h2 : (2 : ℝ) * ρ ≤ εb / 2 := by linarith
      have h1 : dist z S.ζb < εb := by linarith
      exact hεb (by rwa [Metric.mem_ball])

end Work.Repel
