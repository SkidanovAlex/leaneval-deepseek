import Mathlib
import Submission.Work.OddRadon.RadialDefs

namespace Work.OddRadon

/-- If the second datum `Ψ` is nonzero at `α₀ ∈ [0, π/2)`, the two radial functions cannot
coincide there: `R α₀ = r α₀` would force `R α₀ ^ (2n+1) - r α₀ ^ (2n+1) = 0`, hence
`Ψ α₀ = 0 · cos α₀ = 0`. -/
theorem radialSystem_ne_of_psi_ne (n : ℕ) {Φ Ψ : ℝ → ℝ} {R r : ℝ → ℝ}
    (h : RadialSystem n Φ Ψ R r) {α₀ : ℝ} (hα₀ : α₀ ∈ Set.Ico 0 (Real.pi / 2))
    (hΨ : Ψ α₀ ≠ 0) : R α₀ ≠ r α₀ := by
  intro hEq
  have hsub : Set.Ico (0 : ℝ) (Real.pi / 2) ⊆ Set.Icc (0 : ℝ) (Real.pi / 2) :=
    Set.Ico_subset_Icc_self
  have h2 := (h α₀ (hsub hα₀)).2
  rw [hEq, sub_self, zero_mul] at h2
  exact hΨ h2.symm

end Work.OddRadon
