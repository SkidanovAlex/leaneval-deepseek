import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Topology.MetricSpace.Sequences

open Filter
open scoped Topology

set_option autoImplicit false

namespace Commons.Analysis.Sequences

/-- A bounded real sequence all of whose convergent subsequences have the
same limit converges to that limit. -/
theorem tendsto_of_unique_subseq_limit {u : ℕ → ℝ} {L : ℝ}
    (hbdd : Bornology.IsBounded (Set.range u))
    (huniq : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ L' : ℝ,
      Tendsto (u ∘ φ) atTop (𝓝 L') → L' = L) :
    Tendsto u atTop (𝓝 L) := by
  classical
  by_contra hnot
  rw [Metric.tendsto_nhds] at hnot
  push Not at hnot
  obtain ⟨ε, hε0, hεnot⟩ := hnot
  obtain ⟨φ, hφmono, hφfar⟩ := Filter.extraction_of_frequently_atTop hεnot
  have hφfar_le : ∀ n : ℕ, ε ≤ |u (φ n) - L| := by
    intro n
    simpa [Real.dist_eq] using hφfar n
  obtain ⟨a, _ha, ψ, hψmono, htend⟩ :=
    tendsto_subseq_of_bounded (X := ℝ) (s := Set.range u) hbdd (x := fun n => u (φ n))
      (by intro n; exact ⟨φ n, rfl⟩)
  have hcompmono : StrictMono (φ ∘ ψ) := hφmono.comp hψmono
  have hfun : (fun n : ℕ => u (φ n)) ∘ ψ = u ∘ (φ ∘ ψ) := by
    rfl
  have htend' : Tendsto (u ∘ (φ ∘ ψ)) atTop (𝓝 a) := by
    simpa [hfun] using htend
  have haL : a = L := huniq (φ ∘ ψ) hcompmono a htend'
  have hlimL : Tendsto (u ∘ (φ ∘ ψ)) atTop (𝓝 L) := by
    simpa [haL] using htend'
  rw [Metric.tendsto_nhds] at hlimL
  have hE := hlimL (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hE
  have hle : ε ≤ |u (φ (ψ N)) - L| := hφfar_le (ψ N)
  have hlt : |u (φ (ψ N)) - L| < ε / 2 := by
    simpa [Real.dist_eq] using hN N le_rfl
  linarith

end Commons.Analysis.Sequences