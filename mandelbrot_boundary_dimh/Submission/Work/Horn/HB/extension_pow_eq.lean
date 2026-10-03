import Mathlib

/-!
# Value of a `d`-th root of `φ ∘ g` at an isolated point of the excluded set

Setting (piece HB4 of the Horn/basin development, Shishikura Prop. 5.3 / Lemma 5.4).

Let `Ψ` be analytic at `c`, let `ψ` agree with `Ψ` on `W \ Z`, let `(ψ z) ^ d = φ (g z)` on
`W \ Z`, let `φ` be continuous at `g c` and `g` continuous at `c`.  If `c` is an isolated point
of `Z` inside `W` (there is a ball around `c` contained in `W` meeting `Z` only in `c`), then the
power relation extends to `c`:

`(Ψ c) ^ d = φ (g c)`.

The proof is purely topological: on the punctured ball both `(Ψ ·) ^ d` and `φ ∘ g` are defined by
the same expression `(ψ ·) ^ d`, and both are continuous at `c`, so their limits at `c` agree.
-/

open Filter Metric
open scoped Topology

namespace Work.Horn.HB

theorem extension_pow_eq {W Z : Set ℂ} {Ψ ψ φ g : ℂ → ℂ} {c : ℂ} {d : ℕ}
    (hiso : ∃ ε : ℝ, 0 < ε ∧ Metric.ball c ε ⊆ W ∧ Metric.ball c ε ∩ Z = {c})
    (hΨ : AnalyticAt ℂ Ψ c) (hΨeq : ∀ z ∈ W \ Z, Ψ z = ψ z)
    (hpw : ∀ z ∈ W \ Z, (ψ z) ^ d = φ (g z))
    (hφc : ContinuousAt φ (g c)) (hgc : ContinuousAt g c) :
    (Ψ c) ^ d = φ (g c) := by
  obtain ⟨ε, hε, hWsub, hZeq⟩ := hiso
  -- The punctured ball is a punctured neighbourhood of `c`.
  have hmem : Metric.ball c ε ∩ ({c}ᶜ) ∈ 𝓝[≠] c := by
    rw [mem_nhdsWithin]
    exact ⟨Metric.ball c ε, Metric.isOpen_ball, Metric.mem_ball_self hε,
      fun z hz => ⟨hz.1, hz.2⟩⟩
  -- On the punctured ball the two functions coincide.
  have heq : (fun z => Ψ z ^ d) =ᶠ[𝓝[≠] c] (fun z => φ (g z)) := by
    filter_upwards [hmem] with z hz
    obtain ⟨hzb, hzc⟩ := hz
    have hzW : z ∈ W := hWsub hzb
    have hzZ : z ∉ Z := by
      intro hzZ
      have h1 : z ∈ Metric.ball c ε ∩ Z := ⟨hzb, hzZ⟩
      rw [hZeq] at h1
      exact hzc h1
    rw [hΨeq z ⟨hzW, hzZ⟩, hpw z ⟨hzW, hzZ⟩]
  -- Both sides have limits at `c`, and limits are unique.
  have hf : Tendsto (fun z => Ψ z ^ d) (𝓝[≠] c) (𝓝 (Ψ c ^ d)) :=
    (hΨ.continuousAt.pow d).tendsto.mono_left nhdsWithin_le_nhds
  have hg : Tendsto (fun z => φ (g z)) (𝓝[≠] c) (𝓝 (φ (g c))) :=
    (hφc.comp hgc).tendsto.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique_of_eventuallyEq hf hg heq

end Work.Horn.HB
