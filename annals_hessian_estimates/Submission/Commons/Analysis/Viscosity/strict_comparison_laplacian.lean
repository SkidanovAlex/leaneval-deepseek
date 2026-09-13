import Mathlib

namespace Commons.Analysis.Viscosity

open MeasureTheory Metric Set Filter Function in
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace in
theorem strict_comparison_laplacian {n : ℕ} {u v : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n)} {R : ℝ} (hR : 0 < R)
    (hu : ContinuousOn u (closedBall c R))
    (hv : ContDiffOn ℝ 2 v (ball c R)) (hvc : ContinuousOn v (closedBall c R))
    (hvisc : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiffOn ℝ 2 φ (ball c R) →
      ∀ x ∈ ball c R, (∀ᶠ y in 𝓝[ball c R] x, u y - φ y ≤ u x - φ x) →
      0 ≤ Laplacian.laplacian φ x)
    (hstrict : ∀ x ∈ ball c R, Laplacian.laplacian v x < 0)
    (hbd : ∀ y ∈ sphere c R, u y ≤ v y) :
    ∀ y ∈ closedBall c R, u y ≤ v y := by
  by_contra hcon
  push Not at hcon
  obtain ⟨y₀, hy₀, hy₀gt⟩ := hcon
  -- `u - v` is continuous on the closed ball, which is compact, hence attains a maximum
  obtain ⟨x₀, hx₀, hmax⟩ :=
    (isCompact_closedBall c R).exists_isMaxOn (⟨y₀, hy₀⟩ : (closedBall c R).Nonempty)
      (hu.sub hvc)
  have hmax' : ∀ y ∈ closedBall c R, u y - v y ≤ u x₀ - v x₀ :=
    fun y hy => isMaxOn_iff.mp hmax y hy
  -- the maximum value is positive, so the maximiser lies in the open ball
  have hx₀ball : x₀ ∈ ball c R := by
    have hmem : x₀ ∈ ball c R ∪ sphere c R := by
      rw [ball_union_sphere]; exact hx₀
    rcases hmem with h | h
    · exact h
    · have hle : u x₀ ≤ v x₀ := hbd x₀ h
      have hpos := hmax' y₀ hy₀
      linarith
  -- `v` itself is an admissible test function: `u - v` has a max at `x₀`
  have hlocal : ∀ᶠ y in 𝓝[ball c R] x₀, u y - v y ≤ u x₀ - v x₀ :=
    eventually_of_mem self_mem_nhdsWithin
      (fun y hy => hmax' y (ball_subset_closedBall hy))
  exact absurd (hvisc v hv x₀ hx₀ball hlocal) (not_le.mpr (hstrict x₀ hx₀ball))

end Commons.Analysis.Viscosity
