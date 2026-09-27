import Mathlib

namespace Work.KT

/-- A continuous family of complex matrices over a compact metric space is uniformly continuous
w.r.t. the entrywise-sup norm. -/
theorem chain_uniform_continuous_norm_sub {X : Type*} [PseudoMetricSpace X] [CompactSpace X] {n : ℕ}
    (γ : X → Matrix (Fin n) (Fin n) ℂ) (hγ : Continuous γ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x x' : X, dist x x' < δ →
      ‖(fun i j => (γ x - γ x') i j)‖ < ε := by
  -- Reinterpret `γ` as a map into the finite product `Fin n → Fin n → ℂ`, on which the
  -- entrywise-sup norm (the Pi-`ℓ^∞` norm) provides a genuine pseudo-metric space structure.
  have hγ' : Continuous (fun x : X => fun i j => γ x i j) := hγ
  -- Heine–Cantor: a continuous map on a compact uniform space is uniformly continuous.
  have huc : UniformContinuous (fun x : X => fun i j => γ x i j) :=
    CompactSpace.uniformContinuous_of_continuous hγ'
  rcases Metric.uniformContinuous_iff.mp huc ε hε with ⟨δ, hδ, h⟩
  exact ⟨δ, hδ, fun x x' hxx' => by
    have hd := h hxx'
    rwa [dist_eq_norm] at hd⟩

end Work.KT
