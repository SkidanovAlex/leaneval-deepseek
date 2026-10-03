import Mathlib

/-!
# Joint continuity from uniform-on-compacta parameter continuity

This file proves `Work.L62C.continuousOn_pair`, the two-variable continuity statement used in
Lemma 6.2 of Shishikura's paper: a family `β ↦ K β` of functions that is continuous in the
parameter `β` uniformly on compact subsets of `Ω` has a *jointly* continuous evaluation map
`(β, z) ↦ K β z` on `Λ ×ˢ Ω`.

The mathematical point is that `Ω` is an arbitrary subset of `ℂ` (no local compactness is
assumed), so "uniform on compacta" does **not** directly give a neighbourhood on which the
convergence is uniform.  The way out is sequential: a bad sequence `zₙ → z₀` in `Ω` together
with its limit is a compact subset of `Ω`, so uniformity on that particular compact set kills
every violating sequence.
-/

namespace Work.L62C

open Set Function Filter
open scoped Topology

/-- **Uniform closeness near a point of `Ω`.**  If `K β` converges to `K β₀` uniformly on every
compact subset of `Ω` as `β → β₀`, then the convergence is in fact uniform on a relative
neighbourhood of every `z₀ ∈ Ω`: there is `δ > 0` such that `‖K β z - K β₀ z‖ < ε` for all
`β ∈ Λ` with `‖β - β₀‖ < δ` and all `z ∈ Ω` with `‖z - z₀‖ < δ`.

Proof by contradiction: if no such `δ` existed, one would get a sequence `(βₙ, zₙ) → (β₀, z₀)`
with `ε ≤ ‖K βₙ zₙ - K β₀ zₙ‖`.  But `{z₀} ∪ {zₙ}` is a compact subset of `Ω` (a convergent
sequence together with its limit), so applying the hypothesis to it contradicts the inequality
for large `n`. -/
theorem uniform_near {Λ Ω : Set ℂ} {K : ℂ → ℂ → ℂ}
    (hloc : ∀ β₀ ∈ Λ, ∀ S ⊆ Ω, IsCompact S → ∀ ε > 0, ∃ δ > 0,
      ∀ β ∈ Λ, ‖β - β₀‖ < δ → ∀ z ∈ S, ‖K β z - K β₀ z‖ < ε)
    {β₀ z₀ : ℂ} (hβ₀ : β₀ ∈ Λ) (hz₀ : z₀ ∈ Ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ β ∈ Λ, ‖β - β₀‖ < δ → ∀ z ∈ Ω, ‖z - z₀‖ < δ → ‖K β z - K β₀ z‖ < ε := by
  by_contra h
  push Not at h
  -- For every `δ > 0` there is a violating pair `(β, z)`.
  have hseq : ∀ n : ℕ, ∃ β : ℂ, ∃ z : ℂ,
      β ∈ Λ ∧ ‖β - β₀‖ < 1 / ((n : ℝ) + 1) ∧
      z ∈ Ω ∧ ‖z - z₀‖ < 1 / ((n : ℝ) + 1) ∧ ε ≤ ‖K β z - K β₀ z‖ := by
    intro n
    obtain ⟨β, hβ, hbδ, z, hz, hzδ, hbad⟩ := h (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨β, z, hβ, hbδ, hz, hzδ, hbad⟩
  choose b z hb hbδ hz hzδ hbad using hseq
  -- The extracted sequences converge.
  have hztend : Tendsto z atTop (𝓝 z₀) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => le_of_lt (hzδ n))
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hbtend : Tendsto b atTop (𝓝 β₀) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => le_of_lt (hbδ n))
      tendsto_one_div_add_atTop_nhds_zero_nat
  -- Their values together with the limit form a compact subset of `Ω`.
  have hcomp : IsCompact (insert z₀ (Set.range z)) := hztend.isCompact_insert_range
  have hsub : insert z₀ (Set.range z) ⊆ Ω := by
    intro u hu
    rcases hu with rfl | ⟨n, rfl⟩
    · exact hz₀
    · exact hz n
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hloc β₀ hβ₀ _ hsub hcomp ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hbtend) δ₁ hδ₁pos
  have hN' : ‖b N - β₀‖ < δ₁ := by
    have := hN N le_rfl
    rwa [dist_eq_norm] at this
  exact absurd (hδ₁ (b N) (hb N) hN' (z N) (Or.inr ⟨N, rfl⟩)) (not_lt.mpr (hbad N))

/-- **Joint continuity from parameter-continuity that is uniform on compacts.**  If each `K β` is
continuous on `Ω` and, for `β` near `β₀ ∈ Λ`, `K β` is uniformly close to `K β₀` on every compact
subset of `Ω`, then `(β, z) ↦ K β z` is continuous on `Λ ×ˢ Ω`.

Proof: at `(β₀, z₀) ∈ Λ ×ˢ Ω` split
`‖K β z - K β₀ z₀‖ ≤ ‖K β z - K β₀ z‖ + ‖K β₀ z - K β₀ z₀‖`; the second term is handled by
`hcont β₀`, and the first by applying `hloc` to the compact set `{z}`; the resulting ε-δ statement
is exactly `ContinuousOn` for the product. -/
theorem continuousOn_pair {Λ Ω : Set ℂ} {K : ℂ → ℂ → ℂ}
    (hcont : ∀ β ∈ Λ, ContinuousOn (K β) Ω)
    (hloc : ∀ β₀ ∈ Λ, ∀ S ⊆ Ω, IsCompact S → ∀ ε > 0, ∃ δ > 0,
      ∀ β ∈ Λ, ‖β - β₀‖ < δ → ∀ z ∈ S, ‖K β z - K β₀ z‖ < ε) :
    ContinuousOn (fun p : ℂ × ℂ => K p.1 p.2) (Λ ×ˢ Ω) := by
  rw [Metric.continuousOn_iff]
  rintro ⟨β₀, z₀⟩ hp ε hε
  rw [Set.mem_prod] at hp
  obtain ⟨hβ₀, hz₀⟩ := hp
  -- Uniform closeness of `K β` to `K β₀` near `z₀`, from `hloc`.
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ :=
    uniform_near hloc hβ₀ hz₀ (show (0 : ℝ) < ε / 2 by linarith)
  -- Continuity of `K β₀` at `z₀` within `Ω`.
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ :=
    Metric.continuousWithinAt_iff.mp ((hcont β₀ hβ₀) z₀ hz₀) (ε / 2) (by linarith)
  refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, ?_⟩
  rintro ⟨β, z⟩ hq hdist
  rw [Set.mem_prod] at hq
  obtain ⟨hβ, hz⟩ := hq
  rw [Prod.dist_eq] at hdist
  have hβmin : ‖β - β₀‖ < min δ₁ δ₂ := by
    have h1 : dist β β₀ < min δ₁ δ₂ := lt_of_le_of_lt (le_max_left _ _) hdist
    rwa [dist_eq_norm] at h1
  have hzmin : ‖z - z₀‖ < min δ₁ δ₂ := by
    have h1 : dist z z₀ < min δ₁ δ₂ := lt_of_le_of_lt (le_max_right _ _) hdist
    rwa [dist_eq_norm] at h1
  have h1 : dist (K β z) (K β₀ z) < ε / 2 := by
    rw [dist_eq_norm]
    exact hδ₁ β hβ (lt_of_lt_of_le hβmin (min_le_left _ _)) z hz
      (lt_of_lt_of_le hzmin (min_le_left _ _))
  have h2 : dist (K β₀ z) (K β₀ z₀) < ε / 2 :=
    hδ₂ (x := z) hz (by rw [dist_eq_norm]; exact lt_of_lt_of_le hzmin (min_le_right _ _))
  calc dist (K β z) (K β₀ z₀)
      ≤ dist (K β z) (K β₀ z) + dist (K β₀ z) (K β₀ z₀) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add h1 h2
    _ = ε := by ring

end Work.L62C
