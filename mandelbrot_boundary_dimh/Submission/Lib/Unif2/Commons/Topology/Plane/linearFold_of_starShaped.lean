import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic

open Set

namespace Commons.Topology.Plane

/-- Straight-line ("linear") homotopy from the identity to `ψ` on a set `Q`.

If `Q` is star-shaped with respect to `ψ` (each segment `[x, ψ x]` lies in `Q`) and `ψ` is
continuous, fixes `T` pointwise and maps `Q` into `T`, then there is a homotopy `H` on
`Q × [0,1]` that stays in `Q`, starts at the identity, ends in `T`, and is constant on `Q ∩ T`. -/
theorem linearFold_of_starShaped {Q T : Set ℂ} (ψ : ℂ → ℂ) (hcont : Continuous ψ) (hmaps : ∀ x ∈ Q, ψ x ∈ T) (hseg : ∀ x ∈ Q, segment ℝ x (ψ x) ⊆ Q) (hfix : ∀ x ∈ T, ψ x = x) : ∃ H : ℂ × unitInterval → ℂ, ContinuousOn H (Q ×ˢ (univ : Set unitInterval)) ∧ (∀ x ∈ Q, ∀ t : unitInterval, H (x, t) ∈ Q) ∧ (∀ x ∈ Q, H (x, 0) = x) ∧ (∀ x ∈ Q, H (x, 1) ∈ T) ∧ (∀ x ∈ Q, x ∈ T → ∀ t : unitInterval, H (x, t) = x) := by
  refine ⟨fun p => (1 - (p.2 : ℝ)) • p.1 + (p.2 : ℝ) • ψ p.1, ?_, ?_, ?_, ?_, ?_⟩
  · apply Continuous.continuousOn
    have h2 : Continuous fun p : ℂ × unitInterval => ((p.2 : unitInterval) : ℝ) :=
      continuous_subtype_val.comp continuous_snd
    exact ((continuous_const.sub h2).smul continuous_fst).add (h2.smul (hcont.comp continuous_fst))
  · intro x hx t
    exact hseg x hx ⟨1 - (t : ℝ), (t : ℝ), sub_nonneg.mpr t.2.2, t.2.1, by ring, rfl⟩
  · intro x hx
    simp
  · intro x hx
    simpa using hmaps x hx
  · intro x hx hxT t
    change (1 - (t : ℝ)) • x + (t : ℝ) • ψ x = x
    rw [hfix x hxT, ← add_smul, sub_add_cancel, one_smul]

end Commons.Topology.Plane