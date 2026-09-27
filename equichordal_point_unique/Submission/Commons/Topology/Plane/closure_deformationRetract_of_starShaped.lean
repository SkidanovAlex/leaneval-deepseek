import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Commons.Topology.Plane.linearFold_of_starShaped

open Set

namespace Commons.Topology.Plane

/-- **Strong deformation retraction of a subspace from a star-shaped (straight-line) projection.**

Let `Q T ⊆ ℂ`.  If `ψ : ℂ → ℂ` is continuous, maps `Q` into `T`, fixes `T` pointwise, and the
straight segment `[x, ψ x]` stays in `Q` for every `x ∈ Q`, then the subspace `↥Q` strongly
deformation retracts onto `Q ∩ T`, fixing it pointwise. -/
theorem closure_deformationRetract_of_starShaped (Q T : Set ℂ) (ψ : ℂ → ℂ)
    (hcont : Continuous ψ) (hmaps : ∀ x ∈ Q, ψ x ∈ T) (hfix : ∀ x ∈ T, ψ x = x)
    (hseg : ∀ x ∈ Q, segment ℝ x (ψ x) ⊆ Q) :
    ∃ H : ↥Q × unitInterval → ↥Q,
      Continuous H ∧ (∀ x : ↥Q, H (x, 0) = x) ∧
      (∀ x : ↥Q, (H (x, 1) : ℂ) ∈ T) ∧
      (∀ x : ↥Q, (x : ℂ) ∈ T → ∀ t : unitInterval, H (x, t) = x) := by
  let F : ℂ × unitInterval → ℂ := fun p => (1 - (p.2 : ℝ)) • p.1 + (p.2 : ℝ) • ψ p.1
  have hFcont : Continuous F := by
    have h2 : Continuous fun p : ℂ × unitInterval => ((p.2 : unitInterval) : ℝ) :=
      continuous_subtype_val.comp continuous_snd
    exact ((continuous_const.sub h2).smul continuous_fst).add (h2.smul (hcont.comp continuous_fst))
  have hFmem : ∀ p : ↥Q × unitInterval, F (p.1.1, p.2) ∈ Q := by
    rintro ⟨⟨x, hx⟩, t⟩
    exact hseg x hx ⟨1 - (t : ℝ), (t : ℝ), sub_nonneg.mpr t.2.2, t.2.1, by ring, rfl⟩
  refine ⟨fun p => ⟨F (p.1.1, p.2), hFmem p⟩, ?_, ?_, ?_, ?_⟩
  · apply Continuous.subtype_mk
    exact hFcont.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  · intro x
    apply Subtype.ext
    simp [F]
  · intro x
    simpa [F] using hmaps (x : ℂ) x.2
  · intro x hxT t
    apply Subtype.ext
    change (1 - (t : ℝ)) • (x : ℂ) + (t : ℝ) • ψ (x : ℂ) = (x : ℂ)
    rw [hfix (x : ℂ) hxT, ← add_smul, sub_add_cancel, one_smul]

end Commons.Topology.Plane