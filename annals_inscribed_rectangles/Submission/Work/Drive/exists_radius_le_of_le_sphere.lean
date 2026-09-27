import Mathlib

namespace Work.Drive

/-- If `F : ℂ → ℝ` is continuous and strictly below `q` on the sphere of radius `β`,
then there is a radius `σ₁` with `ρ < σ₁ < β` such that `F ≤ q` on the closed annulus
`{z | σ₁ ≤ ‖z‖ ≤ β}`.

The proof takes the compact set `E = {‖z‖ ≤ β, q ≤ F z}` where `F` fails the bound,
and slides the annulus past its outermost point. -/
theorem exists_radius_le_of_le_sphere {F : ℂ → ℝ} (hF : Continuous F) {ρ β q : ℝ} (hρβ : ρ < β)
    (hsphere : ∀ z : ℂ, ‖z‖ = β → F z < q) :
    ∃ σ₁ : ℝ, ρ < σ₁ ∧ σ₁ < β ∧ ∀ z : ℂ, σ₁ ≤ ‖z‖ → ‖z‖ ≤ β → F z ≤ q := by
  set E : Set ℂ := Metric.closedBall (0 : ℂ) β ∩ {z : ℂ | q ≤ F z} with hEdef
  have hEclosed : IsClosed E := Metric.isClosed_closedBall.inter (isClosed_le continuous_const hF)
  have hEcompact : IsCompact E :=
    (isCompact_closedBall (0 : ℂ) β).of_isClosed_subset hEclosed Set.inter_subset_left
  by_cases hne : E.Nonempty
  · -- `E` is nonempty: cut the annulus just above the outermost point of `E`.
    obtain ⟨e, heE, hmax⟩ := hEcompact.exists_isMaxOn hne continuous_norm.continuousOn
    have heβ : ‖e‖ ≤ β := by
      have h1 : e ∈ Metric.closedBall (0 : ℂ) β := heE.1
      simpa [Metric.mem_closedBall, dist_zero_right] using h1
    have heq : q ≤ F e := heE.2
    have hlt : ‖e‖ < β := by
      rcases lt_or_eq_of_le heβ with h | h
      · exact h
      · exact absurd (hsphere e h) (not_lt.mpr heq)
    have hmaxβ : max ρ ‖e‖ < β := max_lt hρβ hlt
    have h1 : ρ ≤ max ρ ‖e‖ := le_max_left _ _
    have h2 : ‖e‖ ≤ max ρ ‖e‖ := le_max_right _ _
    refine ⟨(max ρ ‖e‖ + β) / 2, ?_, ?_, ?_⟩
    · linarith
    · linarith
    · intro z hz1 hz2
      by_contra hcon
      rw [not_le] at hcon
      have hzE : z ∈ E := by
        refine ⟨?_, ?_⟩
        · simpa [Metric.mem_closedBall, dist_zero_right] using hz2
        · exact le_of_lt hcon
      have hzle : ‖z‖ ≤ ‖e‖ := isMaxOn_iff.mp hmax z hzE
      linarith
  · -- `E` is empty: `F < q` on the whole closed ball, so any radius works.
    refine ⟨(ρ + β) / 2, ?_, ?_, ?_⟩
    · linarith
    · linarith
    · intro z hz1 hz2
      by_contra hcon
      rw [not_le] at hcon
      exact hne ⟨z, ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using hz2, le_of_lt hcon⟩⟩

end Work.Drive
