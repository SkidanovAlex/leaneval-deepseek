import Mathlib.Analysis.Normed.Order.Lattice

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif

theorem rho_bounds {a b c d : ℝ} (hab : a < b) (hcd : c < d) {ρ : ℝ → ℝ → ℝ}
    (hρc : ContinuousOn (Function.uncurry ρ) (Set.Icc a b ×ˢ Set.Icc c d))
    (hρp : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, 0 < ρ z θ) :
    (∃ m : ℝ, 0 < m ∧ ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, m ≤ ρ z θ) ∧
    (∀ ε > 0, ∃ δ > 0, ∀ z ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      |z - t| < δ → |ρ z θ - ρ t θ| < ε) := by
  have hK : IsCompact (Set.Icc a b ×ˢ Set.Icc c d) :=
    (isCompact_Icc (a := a) (b := b)).prod (isCompact_Icc (a := c) (b := d))
  constructor
  · obtain ⟨m, hm, hle⟩ :=
      hK.exists_forall_le' hρc (a := 0) (fun p hp => hρp p.1 hp.1 p.2 hp.2)
    exact ⟨m, hm, fun z hz θ hθ => hle (z, θ) ⟨hz, hθ⟩⟩
  · intro ε hε
    have hunif : UniformContinuousOn (Function.uncurry ρ) (Set.Icc a b ×ˢ Set.Icc c d) :=
      hK.uniformContinuousOn_of_continuous hρc
    obtain ⟨δ, hδ, hδ'⟩ := (Metric.uniformContinuousOn_iff.mp hunif) ε hε
    refine ⟨δ, hδ, fun z hz t ht θ hθ hzt => ?_⟩
    have hd : dist (z, θ) (t, θ) < δ := by
      rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, Real.dist_eq]
      exact hzt
    have hres := hδ' (z, θ) ⟨hz, hθ⟩ (t, θ) ⟨ht, hθ⟩ hd
    rwa [Real.dist_eq] at hres

end Work.FTS.StrongEps.LocUnif
